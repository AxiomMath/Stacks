module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.ClosedImmersionPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.StrictlyHenselianGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SupportedSectionsInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimaryVanishing

/-!
# Étale sheaves supported at finitely many closed points

Let `K` be a separably closed field, let `X` be a scheme locally of finite type over `K` and let
`F` be an abelian sheaf on the small étale site of `X` whose support is contained in a finite set
of closed points. Then the positive-degree étale cohomology of `F` vanishes and `F` is generated
by its global sections. This is the finite-support case of [Stacks, Tag 0F1F], on which the
general case rests.

The proof is an induction on the finite set carrying the support. If it is empty then every
geometric stalk of `F` vanishes, so `F` is zero and both conclusions are immediate. For
`insert a s` let `i : Spec κ(a) ⟶ X` be the inclusion of the residue field at the closed point
`a` — a closed immersion, because the point is closed — and let `η : F ⟶ i_* i^{-1} F` be the
unit of the inverse image/direct image adjunction along `i`. Inverse image along `i` inverts `η`,
the counit of that adjunction being an isomorphism by [Stacks, Tag 04CA]; hence `η` is an
epimorphism and the inverse image of its kernel vanishes. The kernel therefore has no support at
`a`, so its support lies in `s` and the inductive hypothesis applies to it. The target
`i_* i^{-1} F` is a direct image from the spectrum of `κ(a)`, which is separably closed because
`X` is locally of finite type over the separably closed `K`; [Stacks, Tag 03QO] gives both
conclusions there, and both transport along the closed immersion. They then pass to `F` through
the short exact sequence `0 ⟶ ker η ⟶ F ⟶ i_* i^{-1} F ⟶ 0`: vanishing by the covariant long
exact sequence of `Ext`, and global generation because the degree-zero part of that same sequence
makes global sections of `η` surjective, so that the two outer counits force the cokernel of the
counit at `F` to vanish.

## Main results

* `AlgebraicGeometry.subsingleton_sheafH_and_epi_counit_of_finite_support` — both conclusions of
  [Stacks, Tag 0F1F] for an abelian sheaf on the small étale site of a scheme locally of finite
  type over a separably closed field whose support is contained in a finite set of closed points.
* `AlgebraicGeometry.subsingleton_sheafH_of_isSepClosed` — positive-degree étale cohomology over
  a separably closed field vanishes, stated at the spectrum of a bare type.
* `AlgebraicGeometry.residueFieldObj` and `AlgebraicGeometry.residueFieldIncl` — the spectrum of
  the residue field at a point of an object of a big étale site, and its inclusion.

## Implementation notes

"Globally generated" is read, as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Main`, as the counit of
`CategoryTheory.constantSheafΓAdj` being an epimorphism, and the degree-`q` cohomology group is
`CategoryTheory.Sheaf.H` at the `Ext` universe `u + 1`. That the latter elaborates on this site
with no hypothesis is `AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf_succ`, installed
as a local instance.

Vanishing over the residue field is routed through
`AlgebraicGeometry.subsingleton_sheafH_of_isSepClosed`, which is stated at `Spec (.of R)` for a
bare `R : Type u` and applies `Stacks.StrictlyHenselian.subsingleton_etaleCohomology` with its
universes pinned. Applying that result directly at `AlgebraicGeometry.residueFieldObj` instead
makes `CategoryTheory.HasExt` synthesis diverge, the site's objects living one universe above its
morphisms.

Two steps of the argument are facts about an arbitrary site and an arbitrary adjunction into an
abelian category rather than about étale cohomology, and are proved as such before the namespace:
surjectivity of global sections of the epimorphism of a short exact sequence whose kernel has no
first cohomology, and stability of generation by global sections under extensions. The first is
the degree-zero part of `CategoryTheory.Abelian.Ext.covariant_sequence_exact₃` transported along
`CategoryTheory.Sheaf.H.equiv₀` and `CategoryTheory.Sheaf.ΓNatIsoSheafSections`.

The induction is `Set.Finite.induction_on`, whose motive ranges over the finite set and its
finiteness proof alone. The sheaf and the containment of its support therefore sit inside the
conclusion of the statement actually proved by induction — otherwise the inductive hypothesis
would speak only about the sheaf at hand, while the step applies it to the kernel of the unit;
the theorem consumed downstream takes them as ordinary arguments instead.

## References

* [Stacks Project, Tag 0F1F](https://stacks.math.columbia.edu/tag/0F1F)
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w v u

/-- **Global sections carry the epimorphism of a short exact sequence whose kernel has no first
cohomology to an epimorphism.** -/
private theorem epi_Γ_map_g_of_shortExact {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] [HasTerminal C] {T : C} (hT : IsTerminal T)
    {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)
    (h1 : Subsingleton (Sheaf.H.{w', w} S.X₁ 1)) :
    Epi ((Sheaf.Γ J AddCommGrpCat.{w}).map S.g) := by
  have hsurj : Function.Surjective (Sheaf.H.map.{w', w} S.g 0) := by
    intro x₃
    obtain ⟨x₂, hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃
      ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))) hS x₃
      (n₁ := 1) rfl (@Subsingleton.elim _ h1 _ _)
    exact ⟨x₂, hx₂⟩
  have hepi : Epi (((sheafSections J AddCommGrpCat.{w}).obj (op T)).map S.g) := by
    refine (AddCommGrpCat.epi_iff_surjective _).2 fun y => ?_
    obtain ⟨x₂, hx₂⟩ := hsurj ((Sheaf.H.equiv₀ S.X₃ hT).symm y)
    refine ⟨Sheaf.H.equiv₀ S.X₂ hT x₂, ?_⟩
    rw [show (((sheafSections J AddCommGrpCat.{w}).obj (op T)).map S.g) =
      S.g.hom.app (op T) from rfl, Sheaf.H.equiv₀_naturality, hx₂,
      AddEquiv.apply_symm_apply]
  have hnat := (Sheaf.ΓNatIsoSheafSections J AddCommGrpCat.{w} hT).hom.naturality S.g
  have h2 : Epi ((Sheaf.Γ J AddCommGrpCat.{w}).map S.g ≫
      (Sheaf.ΓNatIsoSheafSections J AddCommGrpCat.{w} hT).hom.app S.X₃) := by
    rw [hnat]
    exact epi_comp _ _
  have h3 : Epi (((Sheaf.Γ J AddCommGrpCat.{w}).map S.g ≫
      (Sheaf.ΓNatIsoSheafSections J AddCommGrpCat.{w} hT).hom.app S.X₃) ≫
      inv ((Sheaf.ΓNatIsoSheafSections J AddCommGrpCat.{w} hT).hom.app S.X₃)) := by
    have := h2
    exact epi_comp _ _
  rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h3

/-- **Generation by global sections passes to an extension.** -/
private theorem epi_counit_of_epi_counit_kernel {A S : Type*} [Category* A] [Category* S]
    [Abelian S] {L : A ⥤ S} {R : S ⥤ A} (adj : L ⊣ R) {F N : S} (η : F ⟶ N) [Epi η]
    (h1 : Epi (adj.counit.app (kernel η))) (h2 : Epi (adj.counit.app N))
    (h3 : Epi (L.map (R.map η))) :
    Epi (adj.counit.app F) := by
  have := h1
  have := h2
  have := h3
  have hnatk : L.map (R.map (kernel.ι η)) ≫ adj.counit.app F =
      adj.counit.app (kernel η) ≫ kernel.ι η := adj.counit.naturality (kernel.ι η)
  have hnat : L.map (R.map η) ≫ adj.counit.app N = adj.counit.app F ≫ η :=
    adj.counit.naturality η
  have ha : kernel.ι η ≫ cokernel.π (adj.counit.app F) = 0 := by
    rw [← cancel_epi (adj.counit.app (kernel η)), comp_zero, ← Category.assoc, ← hnatk,
      Category.assoc, cokernel.condition, comp_zero]
  have hc : η ≫ Abelian.epiDesc η (cokernel.π (adj.counit.app F)) ha =
      cokernel.π (adj.counit.app F) := Abelian.comp_epiDesc η _ ha
  have hc0 : Abelian.epiDesc η (cokernel.π (adj.counit.app F)) ha = 0 := by
    have hcomp : Epi (L.map (R.map η) ≫ adj.counit.app N) := epi_comp _ _
    rw [← cancel_epi (L.map (R.map η) ≫ adj.counit.app N), comp_zero, hnat, Category.assoc, hc]
    exact cokernel.condition _
  have hzero : cokernel.π (adj.counit.app F) = 0 := by rw [← hc, hc0, comp_zero]
  refine Preadditive.epi_of_isZero_cokernel _ ?_
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (cokernel.π (adj.counit.app F)), hzero]
  simp

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ

/-- **Positive-degree étale cohomology over a separably closed field vanishes.** A separably
closed field is a strictly henselian local ring, so this is
`Stacks.StrictlyHenselian.subsingleton_etaleCohomology`.

Stated at the spectrum of a bare `R : Type u` rather than at an object of the site: that is what
keeps `CategoryTheory.HasExt` synthesis from diverging at the universe of the coefficients. -/
public theorem subsingleton_sheafH_of_isSepClosed (B : BigEtaleSite.{u}) (R : Type u)
    [Field R] [IsSepClosed R] (hR : B.Contains (Spec (.of R)))
    (G : Sheaf (SmallEtale.topology B (Spec (.of R)) hR) AddCommGrpCat.{u + 1})
    (q : ℕ) (hq : 1 ≤ q) : Subsingleton (Sheaf.H.{u + 1, u + 1} G q) :=
  let : StrictlyHenselianLocalRing R := StrictlyHenselianLocalRing.of_isSepClosed R
  Stacks.StrictlyHenselian.subsingleton_etaleCohomology.{u, u + 1} B R hR G q hq

/-- **The spectrum of the residue field at a point, as an object of the big étale site.** It is
below the size cutoff because the morphism from it to `X` is a quasi-compact monomorphism. -/
public def residueFieldObj (B : BigEtaleSite.{u}) (X : B.Scheme) (x : X.obj) : B.Scheme :=
  ⟨Spec (.of (ToType (X.obj.residueField x))),
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact (X.obj.fromSpecResidueField x))
      X.property⟩

/-- **The inclusion of the spectrum of the residue field at a point into the scheme**, as a
morphism of the big étale site: `AlgebraicGeometry.Scheme.fromSpecResidueField` itself. It is a
closed immersion exactly when the point is closed. -/
public def residueFieldIncl (B : BigEtaleSite.{u}) (X : B.Scheme) (x : X.obj) :
    residueFieldObj B X x ⟶ X :=
  ⟨X.obj.fromSpecResidueField x⟩

/-- A point is outside the support of a sheaf iff the stalk at a geometric point above it
vanishes. -/
private theorem not_mem_supportSheaf_iff_isZero_etaleStalk (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : SmallEtaleAbelianSheaf B X) (p : GeometricPoint X.obj) (x : X.obj)
    (hp : GeometricPoint.LiesOver p x) :
    x ∉ supportSheaf B X.obj X.property F ↔ IsZero (etaleStalk B X.obj X.property p F.obj) := by
  rw [mem_supportSheaf_iff B X.obj X.property F p x hp, not_not, isZero_etaleStalk_ulift_iff]

/-- **A sheaf with empty support is zero.** -/
private theorem isZero_of_supportSheaf_subset_empty (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : SmallEtaleAbelianSheaf B X) (hF : supportSheaf B X.obj X.property F ⊆ ∅) :
    IsZero F :=
  isZero_of_forall_isZero_etaleStalk B X.obj X.property F fun p =>
    (not_mem_supportSheaf_iff_isZero_etaleStalk B X F p _ rfl).1 fun h => hF h

section ClosedImmersion

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)

/-- The inverse image/direct image adjunction of abelian sheaves. -/
private abbrev adjunctionAb :
    smallEtalePullbackAbOfScheme B i ⊣ SmallEtale.etalePushforward.{u, u + 1} B i :=
  (smallEtaleBaseChange B i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Z.obj Z.property)

variable [IsClosedImmersion (B.inclusion.map i)]

/-- The inverse image of the unit along a closed immersion is an isomorphism. -/
private theorem isIso_pullbackAb_map_unit (F : SmallEtaleAbelianSheaf B X) :
    IsIso ((smallEtalePullbackAbOfScheme B i).map ((adjunctionAb B i).unit.app F)) := by
  have hid : (smallEtalePullbackAbOfScheme B i).map ((adjunctionAb B i).unit.app F) ≫
      (adjunctionAb B i).counit.app ((smallEtalePullbackAbOfScheme B i).obj F) = 𝟙 _ :=
    (adjunctionAb B i).left_triangle_components F
  have h : IsIso ((smallEtalePullbackAbOfScheme B i).map ((adjunctionAb B i).unit.app F) ≫
      (adjunctionAb B i).counit.app ((smallEtalePullbackAbOfScheme B i).obj F)) := by
    rw [hid]; exact IsIso.id _
  exact IsIso.of_isIso_comp_right _
    ((adjunctionAb B i).counit.app ((smallEtalePullbackAbOfScheme B i).obj F))

/-- The unit of the adjunction along a closed immersion is an epimorphism. -/
private theorem epi_adjunctionAb_unit_app (F : SmallEtaleAbelianSheaf B X) :
    Epi ((adjunctionAb B i).unit.app F) :=
  have := isIso_pullbackAb_map_unit B i F
  epi_of_epi_sheafPullback B i ((smallEtalePullbackAbOfScheme B i).obj F)
    ((adjunctionAb B i).unit.app F) inferInstance

/-- The inverse image of the kernel of the unit vanishes. -/
private theorem isZero_pullbackAb_kernel_unit (F : SmallEtaleAbelianSheaf B X) :
    IsZero ((smallEtalePullbackAbOfScheme B i).obj (kernel ((adjunctionAb B i).unit.app F))) := by
  have := isIso_pullbackAb_map_unit B i F
  have h1 :
      (smallEtalePullbackAbOfScheme B i).map (kernel.ι ((adjunctionAb B i).unit.app F)) = 0 := by
    rw [← cancel_mono ((smallEtalePullbackAbOfScheme B i).map ((adjunctionAb B i).unit.app F)),
      zero_comp, ← Functor.map_comp, kernel.condition, Functor.map_zero]
  have hmono : Mono ((smallEtalePullbackAbOfScheme B i).map
      (kernel.ι ((adjunctionAb B i).unit.app F))) :=
    (smallEtalePullbackAbOfScheme B i).map_mono _
  rw [IsZero.iff_id_eq_zero,
    ← cancel_mono
      ((smallEtalePullbackAbOfScheme B i).map (kernel.ι ((adjunctionAb B i).unit.app F))), h1]
  simp

/-- A sheaf killed by inverse image along a closed immersion has support disjoint from the
image of that closed immersion. -/
private theorem not_mem_supportSheaf_of_isZero_pullbackAb (Q : SmallEtaleAbelianSheaf B X)
    (hQ : IsZero ((smallEtalePullbackAbOfScheme B i).obj Q)) {x : X.obj}
    (hx : x ∈ Set.range (B.inclusion.map i).base) :
    x ∉ supportSheaf B X.obj X.property Q := by
  refine (not_mem_supportSheaf_iff_isZero_etaleStalk B X Q (GeometricPoint.ofPoint X.obj x) x
    (GeometricPoint.ofPoint_liesOver X.obj x)).2
    (isZero_etaleStalk_of_isZero_sheafPullback B i Q hQ (GeometricPoint.ofPoint X.obj x) ?_)
  rw [GeometricPoint.ofPoint_liesOver X.obj x]
  exact hx

/-- The inductive step: adding one point of the closed subscheme `Za` to the support. -/
private theorem step_of_closedImmersion {B : BigEtaleSite.{u}} {Za X : B.Scheme} (i : Za ⟶ X)
    [IsClosedImmersion (B.inclusion.map i)]
    (hvan : ∀ (G : SmallEtaleAbelianSheaf B Za) (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H.{u + 1, u + 1} G q))
    (hgen : ∀ G : SmallEtaleAbelianSheaf B Za,
      Epi ((constantSheafΓAdj (SmallEtale.topology B Za.obj Za.property)
        AddCommGrpCat.{u + 1}).counit.app G))
    (a : X.obj) (ha : a ∈ Set.range (B.inclusion.map i).base) (s : Set X.obj)
    (ih : ∀ G : SmallEtaleAbelianSheaf B X, supportSheaf B X.obj X.property G ⊆ s →
      (∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{u + 1, u + 1} G q)) ∧
        Epi ((constantSheafΓAdj (SmallEtale.topology B X.obj X.property)
          AddCommGrpCat.{u + 1}).counit.app G))
    (F : SmallEtaleAbelianSheaf B X)
    (hF : supportSheaf B X.obj X.property F ⊆ insert a s) :
    (∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{u + 1, u + 1} F q)) ∧
      Epi ((constantSheafΓAdj (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.{u + 1}).counit.app F) := by
  have hepi : Epi ((adjunctionAb B i).unit.app F) := epi_adjunctionAb_unit_app B i F
  have hk0 : IsZero ((smallEtalePullbackAbOfScheme B i).obj
      (kernel ((adjunctionAb B i).unit.app F))) :=
    isZero_pullbackAb_kernel_unit B i F
  have hsub : supportSheaf B X.obj X.property
      (kernel ((adjunctionAb B i).unit.app F)) ⊆ s := by
    intro y hy
    have hy1 : y ∈ insert a s :=
      hF (supportSheaf_subset_of_mono B X.obj X.property _ F
        (kernel.ι ((adjunctionAb B i).unit.app F)) hy)
    rcases Set.mem_insert_iff.mp hy1 with rfl | hy2
    · exact absurd hy (not_mem_supportSheaf_of_isZero_pullbackAb B i _ hk0 ha)
    · exact hy2
  obtain ⟨ihvan, ihgen⟩ := ih (kernel ((adjunctionAb B i).unit.app F)) hsub
  have hNvan : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{u + 1, u + 1}
      ((smallEtalePullbackAbOfScheme B i ⋙ SmallEtale.etalePushforward.{u, u + 1} B i).obj F)
        q) := by
    intro q hq
    have := hvan ((smallEtalePullbackAbOfScheme B i).obj F) q hq
    exact (sheafHEtalePushforwardAddEquiv B i ((smallEtalePullbackAbOfScheme B i).obj F)
      q).symm.toEquiv.subsingleton
  have hNgen : Epi ((constantSheafΓAdj (SmallEtale.topology B X.obj X.property)
      AddCommGrpCat.{u + 1}).counit.app
        ((SmallEtale.etalePushforward.{u, u + 1} B i).obj
          ((smallEtalePullbackAbOfScheme B i).obj F))) :=
    epi_constantSheafΓAdj_counit_etalePushforward B i ((smallEtalePullbackAbOfScheme B i).obj F)
      (hgen ((smallEtalePullbackAbOfScheme B i).obj F))
  have hSE : (ShortComplex.mk (kernel.ι ((adjunctionAb B i).unit.app F))
      ((adjunctionAb B i).unit.app F)
      (kernel.condition ((adjunctionAb B i).unit.app F))).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _
        (kernelIsKernel ((adjunctionAb B i).unit.app F))
      mono_f := inferInstance
      epi_g := inferInstance }
  refine ⟨fun q hq => ?_, ?_⟩
  · have := ihvan q hq
    have := hNvan q hq
    exact Stacks.EtaleCohomology.subsingleton_sheafCohomology_X₂_of_shortExact hSE q
  · have hΓ : Epi ((Sheaf.Γ (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.{u + 1}).map ((adjunctionAb B i).unit.app F)) :=
      epi_Γ_map_g_of_shortExact (SmallEtale.finalIsTerminal B X.obj X.property) hSE
        (ihvan 1 one_pos)
    exact epi_counit_of_epi_counit_kernel
      (constantSheafΓAdj (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      ((adjunctionAb B i).unit.app F) ihgen hNgen inferInstance

end ClosedImmersion

/-- Induction on the finite set of closed points carrying the support. -/
private theorem subsingleton_sheafH_and_epi_counit_aux
    (B : BigEtaleSite.{u}) (K : Type u) [Field K] [IsSepClosed K] (X : B.Scheme)
    (f : X.obj ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (Z : Set X.obj) (hZfin : Z.Finite) :
    ∀ (_ : ∀ x ∈ Z, IsClosed ({x} : Set X.obj)) (F : SmallEtaleAbelianSheaf B X),
      supportSheaf B X.obj X.property F ⊆ Z →
      (∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{u + 1, u + 1} F q)) ∧
        Epi ((constantSheafΓAdj (SmallEtale.topology B X.obj X.property)
          AddCommGrpCat.{u + 1}).counit.app F) := by
  induction Z, hZfin using Set.Finite.induction_on with
  | empty =>
    intro _ F hF
    have hzero := isZero_of_supportSheaf_subset_empty B X F hF
    exact ⟨fun q _ => Sheaf.subsingleton_H_of_isZero hzero q,
      ⟨fun g h _ => hzero.eq_of_src g h⟩⟩
  | @insert a s _ha _hs ih =>
    intro hZcl F hF
    have hacl : IsClosed ({a} : Set X.obj) := hZcl a (Set.mem_insert a s)
    have : IsClosedImmersion (B.inclusion.map (residueFieldIncl B X a)) :=
      isClosed_singleton_iff_isClosedImmersion.mp hacl
    let : IsSepClosed (ToType (X.obj.residueField a)) :=
      isSepClosed_residueField_of_isClosed f a hacl
    exact step_of_closedImmersion (residueFieldIncl B X a)
      (fun G q hq => subsingleton_sheafH_of_isSepClosed B (ToType (X.obj.residueField a))
        (residueFieldObj B X a).property G q hq)
      (fun G => Stacks.StrictlyHenselian.epi_constantSheafΓAdj_counit B
        (ToType (X.obj.residueField a)) (residueFieldObj B X a).property G)
      a ((Scheme.range_fromSpecResidueField a).ge rfl) s
      (fun G hG => ih (fun x hx => hZcl x (Set.mem_insert_of_mem a hx)) G hG) F hF

/-- **Both conclusions of [Stacks, Tag 0F1F] for a sheaf supported at finitely many closed
points.** Let `K` be a separably closed field, let `X` be a scheme locally of finite type over
`K` and let `F` be an abelian sheaf on the small étale site of `X` whose support is contained in
a finite set `Z` of closed points. Then `H^q(X, F) = 0` for `q > 0`, and `F` is globally
generated: the constant sheaf on its group of global sections surjects onto it.

The induction is on `Z`. For `Z` empty the sheaf is zero. One point `a` at a time is removed by
the unit `F ⟶ i_* i^{-1} F` of the adjunction along the closed immersion `i` of the residue
field at `a`: the unit is an epimorphism, its kernel has support one point smaller, and its
target comes by direct image from the spectrum of the separably closed field `κ(a)`, where both
conclusions hold by [Stacks, Tag 03QO]. -/
public theorem subsingleton_sheafH_and_epi_counit_of_finite_support
    (B : BigEtaleSite.{u}) (K : Type u) [Field K] [IsSepClosed K] (X : B.Scheme)
    (f : X.obj ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (Z : Set X.obj) (hZfin : Z.Finite) (hZcl : ∀ x ∈ Z, IsClosed ({x} : Set X.obj))
    (F : SmallEtaleAbelianSheaf B X)
    (hsupp : supportSheaf B X.obj X.property F ⊆ Z) :
    (∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{u + 1, u + 1} F q)) ∧
      Epi ((constantSheafΓAdj (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.{u + 1}).counit.app F) :=
  subsingleton_sheafH_and_epi_counit_aux B K X f Z hZfin hZcl F hsupp

end AlgebraicGeometry

end
