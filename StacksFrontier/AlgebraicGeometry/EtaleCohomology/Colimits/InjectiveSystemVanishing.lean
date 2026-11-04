module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystemSectionsColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsAtQcqsObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FilteredColimitOfPresheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveSheafVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctorEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.CechProductMapExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalVanishingFromCechVanishing

/-!
# Vanishing of the higher cohomology of a colimit of injective sheaves

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms, and let `𝒢 = colim f_i⁻¹𝒢_i` be the colimit on the
small étale site of `X` of the inverse images of a system of injective abelian sheaves. The case
`p > 0` of [Stacks, Tag 09YQ] for such a system says that `H^p(X, 𝒢) = 0`. Its proof is Čech
theoretic: the coverings of `X` by finitely many objects quasi-compact and separated over `X` are
cofinal and stable under fibre products ([Stacks, Tag 03F9] then applies), and along such a
covering, which comes from a stage `X_{i₀}`
the Čech complex of `𝒢` is that of the direct image of `𝒢` to `X_{i₀}`, which on the fibre
products of the covering is elementwise the filtered colimit of the direct images of the `𝒢_k`
(the degree zero case of [Stacks, Tag 09YQ]); the Čech complexes of the latter are exact, the
`𝒢_k` being injective. This file provides the Čech side of that argument.

## Main definitions

* `Stacks.CechSite.familyOfIso`, `Stacks.CechSite.homOverOfIso` — a family isomorphic to a given
  one, and the morphism of families comparing them.

## Main results

* `Stacks.CechSite.isZero_cechCohomology_of_iso` — Čech cohomology is invariant under
  isomorphism of families.
* `Stacks.EtaleCohomology.isZero_cechCohomology_pushforward_of_injective` — the Čech cohomology
  of the direct image of an injective sheaf vanishes in positive degrees.
* `Stacks.EtaleCohomology.isZero_cechCohomology_map_of_injective` — the Čech cohomology of the
  colimit of a system of injective sheaves along the base change of a family of a stage vanishes
  in positive degrees.
* `Stacks.EtaleCohomology.isZero_cechCohomology_of_injective` — the same along a finite covering
  by objects with affine underlying schemes of an object quasi-compact and separated over the
  limit, the covering being descended to a stage.
* `Stacks.EtaleCohomology.EtaleSheafSystem.subsingleton_H_of_injective` — **the higher
  cohomology of the colimit of a system of injective sheaves vanishes**.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.CechSite

universe u

namespace Stacks.CechSite

section IsoFamilies

variable {C : Type*} [Category* C] {U V : C} (E : PreZeroHypercover.{u} U) (Y : E.I₀ → C)
  (g : ∀ i, Y i ⟶ V) (e : U ≅ V) (eX : ∀ i, E.X i ≅ Y i)
  (hw : ∀ i, (eX i).hom ≫ g i = E.f i ≫ e.hom)

/-- The family `{Y_i → V}` indexed like `E`. -/
abbrev familyOfIso : PreZeroHypercover.{u} V where
  I₀ := E.I₀
  X := Y
  f := g

/-- The morphism of families induced by isomorphisms of the members over an isomorphism of
the targets. -/
abbrev homOverOfIso : E.HomOver (familyOfIso E Y g) e.hom where
  s₀ i := i
  h₀ i := (eX i).hom
  w₀ i := hw i

include hw in
/-- The inverse morphism of families. -/
abbrev homOverOfIsoInv : (familyOfIso E Y g).HomOver E e.inv where
  s₀ i := i
  h₀ i := (eX i).inv
  w₀ i := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hw i, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

variable [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (g (i a)))]

include hw in
/-- The maps of iterated fibre products induced by `homOverOfIso` and its inverse compose to the
identity. -/
theorem cechProductMap_homOverOfIso_comp (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    cechProductMap E (familyOfIso E Y g) (homOverOfIso E Y g e eX hw) n i ≫
        cechProductMap (familyOfIso E Y g) E (homOverOfIsoInv E Y g e eX hw) n i = 𝟙 _ := by
  refine cechProduct_left_hom_ext E n i fun b ↦ ?_
  rw [Category.assoc, cechProductMap_comp_π_left_anyUniverses,
    cechProductMap_comp_π_left_anyUniverses_assoc, Category.id_comp]
  exact (congrArg (_ ≫ ·) (eX (i b)).hom_inv_id).trans (Category.comp_id _)

include hw in
/-- The maps of iterated fibre products induced by the inverse of `homOverOfIso` and by
`homOverOfIso` compose to the identity. -/
theorem cechProductMap_homOverOfIsoInv_comp (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    cechProductMap (familyOfIso E Y g) E (homOverOfIsoInv E Y g e eX hw) n i ≫
        cechProductMap E (familyOfIso E Y g) (homOverOfIso E Y g e eX hw) n i = 𝟙 _ :=
  cechProductMap_homOverOfIso_comp (familyOfIso E Y g) E.X E.f e.symm
    (fun i ↦ (eX i).symm) (homOverOfIsoInv E Y g e eX hw).w₀ n i

private theorem map_op_comp_eq_id {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (F : 𝒞ᵒᵖ ⥤ 𝒟)
    {X Y : 𝒞} (f : X ⟶ Y) (g : Y ⟶ X) (h : g ≫ f = 𝟙 _) : F.map f.op ≫ F.map g.op = 𝟙 _ := by
  rw [← F.map_comp, ← op_comp, h, op_id, F.map_id]

private theorem pi_inv_chain {𝒜 : Type*} [Category* 𝒜] {κ : Type*} {P Q : κ → 𝒜}
    [HasProduct P] [HasProduct Q] (a : ∏ᶜ Q ⟶ ∏ᶜ P) (b : ∏ᶜ P ⟶ ∏ᶜ Q) (c : ∀ i, Q i ⟶ P i)
    (d : ∀ i, P i ⟶ Q i) (ha : ∀ i, a ≫ Pi.π P i = Pi.π Q i ≫ c i)
    (hb : ∀ i, b ≫ Pi.π Q i = Pi.π P i ≫ d i) (hcd : ∀ i, c i ≫ d i = 𝟙 _) : a ≫ b = 𝟙 _ :=
  Pi.hom_ext _ _ fun i ↦ by
    rw [Category.assoc, hb, reassoc_of% (ha i), hcd, Category.comp_id, Category.id_comp]

/-- The refinement map of Čech complexes of `homOverOfIso` followed by that of its inverse is the
identity in each degree. -/
private theorem cechComplexMap_f_homOverOfIso_comp {A : Type*} [Category* A] [Preadditive A]
    [HasProducts.{u} A] (F : Cᵒᵖ ⥤ A) (n : ℕ) :
    (cechComplexMap E (familyOfIso E Y g) (homOverOfIso E Y g e eX hw) F).f n ≫
      (cechComplexMap (familyOfIso E Y g) E (homOverOfIsoInv E Y g e eX hw) F).f n = 𝟙 _ :=
  pi_inv_chain _ _ _ _
    (cechComplexMap_f_Pi_π E (familyOfIso E Y g) (homOverOfIso E Y g e eX hw) F n)
    (cechComplexMap_f_Pi_π (familyOfIso E Y g) E (homOverOfIsoInv E Y g e eX hw) F n)
    (fun i ↦ map_op_comp_eq_id F _ _ (cechProductMap_homOverOfIsoInv_comp E Y g e eX hw n i))

include hw in
/-- **Isomorphic families have isomorphic Čech complexes**, through the refinement map of
`Stacks.CechSite.cechComplexMap`. -/
theorem isIso_cechComplexMap_homOverOfIso {A : Type*} [Category* A] [Preadditive A]
    [HasProducts.{u} A] (F : Cᵒᵖ ⥤ A) :
    IsIso (cechComplexMap E (familyOfIso E Y g) (homOverOfIso E Y g e eX hw) F) := by
  have : ∀ n, IsIso ((cechComplexMap E (familyOfIso E Y g) (homOverOfIso E Y g e eX hw) F).f n) :=
    fun n ↦ ⟨(cechComplexMap (familyOfIso E Y g) E (homOverOfIsoInv E Y g e eX hw) F).f n,
      cechComplexMap_f_homOverOfIso_comp E Y g e eX hw F n,
      cechComplexMap_f_homOverOfIso_comp (familyOfIso E Y g) E.X E.f e.symm
        (fun i ↦ (eX i).symm) (homOverOfIsoInv E Y g e eX hw).w₀ F n⟩
  exact HomologicalComplex.Hom.isIso_of_components _

include hw in
/-- Vanishing of Čech cohomology transfers along an isomorphism of families. -/
theorem isZero_cechCohomology_of_iso {A : Type*} [Category* A] [Abelian A] [HasProducts.{u} A]
    (F : Cᵒᵖ ⥤ A) (p : ℕ) (h : IsZero (cechCohomology (familyOfIso E Y g) F p)) :
    IsZero (cechCohomology E F p) := by
  have := isIso_cechComplexMap_homOverOfIso E Y g e eX hw F
  exact h.of_iso ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) p).mapIso
    (asIso (cechComplexMap E (familyOfIso E Y g) (homOverOfIso E Y g e eX hw) F))).symm

end IsoFamilies

end Stacks.CechSite

namespace Stacks.EtaleCohomology

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D}

/-- Base change of small étale sites preserves the iterated fibre products of a family. -/
theorem isIso_cechProductMapOfFunctor_smallEtaleBaseChange {X Y : Scheme.{u}} (f : Y ⟶ X)
    {U : X.Etale} (E : PreZeroHypercover.{u} U) (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    IsIso (cechProductMapOfFunctor (smallEtaleBaseChange f) E n i) := by
  have := Stacks.Sites.preservesLimit_fibreProducts_overPost (smallEtaleBaseChange f) E
    (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) n i
  exact isIso_cechProductMapOfFunctor _ _ n i

/-- **The Čech cohomology of the direct image of an injective sheaf vanishes** in positive
degrees: along a family of the small étale site of `X`, the Čech complex of the direct image of
an injective sheaf on `Y` is the Čech complex of that sheaf along the base change of the
family. -/
theorem isZero_cechCohomology_pushforward_of_injective {X Y : Scheme.{u}} (f : Y ⟶ X)
    {U : X.Etale} (E : PreZeroHypercover.{u} U) (J : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    [Injective J] (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology E ((smallEtalePushforwardAb f).obj J).obj p) :=
  cechCohomology_isZero_of_isZero_of_functor (smallEtaleBaseChange f) E J.obj
    (isIso_cechProductMapOfFunctor_smallEtaleBaseChange f E) p
    (injective_sheaf_cechCohomology_isZero.{u + 1, u, u, u + 1} (E.map (smallEtaleBaseChange f))
      J p hp)

/-! ### Objects of the small étale site and their fibre products -/

section Objects

/-- The vertex of a limiting wide pullback cone is the underlying object of the product of the
corresponding objects of the slice category. -/
noncomputable def piOverLeftIsoOfIsLimit {C : Type*} [Category* C] {U : C} {α : Type*}
    {Y : α → C} {f : ∀ a, Y a ⟶ U} [HasProduct (fun a ↦ Over.mk (f a))]
    (t : WidePullbackCone f) (ht : IsLimit t) : (∏ᶜ fun a ↦ Over.mk (f a)).left ≅ t.pt := by
  let fan : Fan (fun a ↦ Over.mk (f a)) :=
    Fan.mk (Over.mk t.base) (fun a ↦ Over.homMk (t.π a) (t.condition a))
  have hfan : IsLimit fan := by
    refine Fan.IsLimit.mk _ (fun s ↦ Over.homMk
      (WidePullbackCone.IsLimit.lift ht s.pt.hom (fun a ↦ (s.proj a).left)
        (fun a ↦ Over.w (s.proj a))) ?_) ?_ ?_
    · exact WidePullbackCone.IsLimit.lift_base ht _ _ _
    · intro s a
      apply Over.OverMorphism.ext
      exact WidePullbackCone.IsLimit.lift_π ht _ _ _ a
    · intro s m hm
      apply Over.OverMorphism.ext
      refine WidePullbackCone.IsLimit.hom_ext ht ?_ ?_
      · change Over.Hom.left m ≫ t.base =
          WidePullbackCone.IsLimit.lift ht s.pt.hom (fun a ↦ Over.Hom.left (s.proj a))
            (fun a ↦ Over.w (s.proj a)) ≫ t.base
        rw [WidePullbackCone.IsLimit.lift_base]
        exact Over.w m
      · intro a
        change Over.Hom.left m ≫ t.π a =
          WidePullbackCone.IsLimit.lift ht s.pt.hom (fun b ↦ Over.Hom.left (s.proj b))
            (fun b ↦ Over.w (s.proj b)) ≫ t.π a
        rw [WidePullbackCone.IsLimit.lift_π]
        exact congrArg (fun g ↦ g.left) (hm a)
  exact (Over.forget U).mapIso ((limit.isLimit _).conePointUniqueUpToIso hfan)

variable {X : Scheme.{u}}

/-- **Cofinal finite affine coverings.** Over a quasi-compact and quasi-separated scheme, every
covering sieve of an object quasi-compact and separated over the base contains a finite covering
family by objects with affine underlying scheme, which belongs to
`Stacks.EtaleCohomology.qcSepCovering`. -/
theorem exists_affine_qcSepCovering_le [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Etale)
    (hU : U ∈ qcSeparatedOver X) (R : Sieve U) (hR : R ∈ X.smallEtaleTopology U) :
    ∃ E ∈ qcSepCovering X U, (∀ i, IsAffine (E.X i).left) ∧ E.sieve₀ ≤ R := by
  have := compactSpace_left_of_mem_qcSeparatedOver hU
  obtain ⟨E, hfin, haff, hcov, hle⟩ := exists_finite_isAffine_covering_le U R hR
  exact ⟨E, ⟨hfin, hU, fun i ↦ have := haff i; mem_qcSeparatedOver_of_isAffine _, hcov⟩, haff, hle⟩

/-- The iterated fibre products of a family of objects of `qcqsEtaleObjects X` over an object of
`qcqsEtaleObjects X` have quasi-compact and quasi-separated underlying scheme. -/
theorem compactSpace_and_quasiSeparatedSpace_pi_of_mem_qcqsEtaleObjects {U₀ : X.Etale}
    (hU : U₀ ∈ qcqsEtaleObjects X) {n : ℕ} {Z : Fin (n + 1) → X.Etale} (ψ : ∀ b, Z b ⟶ U₀)
    (hZ : ∀ b, Z b ∈ qcqsEtaleObjects X) :
    CompactSpace ((∏ᶜ fun b ↦ Over.mk (ψ b)) : Over U₀).left.left ∧
      QuasiSeparatedSpace ((∏ᶜ fun b ↦ Over.mk (ψ b)) : Over U₀).left.left := by
  obtain ⟨tc, ⟨htc⟩, hB⟩ := Stacks.Cohomology.exists_widePullback_in (qcqsEtaleObjects X)
    (fun f g hV hW hU ↦ exists_pullbackCone_mem_qcqsEtaleObjects f g hV hW hU) hU (n + 1) Z ψ hZ
  let k := (Scheme.Etale.forget _ ⋙ Over.forget _).mapIso (piOverLeftIsoOfIsLimit tc htc)
  have : CompactSpace ((Scheme.Etale.forget _ ⋙ Over.forget _).obj tc.pt) := hB.1
  have : QuasiSeparatedSpace ((Scheme.Etale.forget _ ⋙ Over.forget _).obj tc.pt) := hB.2
  exact ⟨k.inv.homeomorph.compactSpace,
    (quasiSeparatedSpace_congr k.hom.homeomorph).mpr inferInstance⟩

end Objects

/-- The objects of the small étale site of the limit `X = lim X_i` whose underlying scheme is
quasi-compact and quasi-separated and which lie over the base change `V₀ ×_{X_i} X` of an object
`V₀` of the small étale site of some stage `X_i` with quasi-compact and quasi-separated
underlying scheme. When the stages are quasi-compact and quasi-separated, every object of
`qcqsEtaleObjects X` qualifies, with `V₀ = X_i`; in general they are the objects over which the
cohomology of a colimit of a system of sheaves is computed from the stages. -/
def qcqsOverStageObjects (c : Cone D) : Set c.pt.Etale :=
  {W | W ∈ qcqsEtaleObjects c.pt ∧ ∃ (i : Iᵒᵖ) (V₀ : (D.obj i).Etale),
    V₀ ∈ qcqsEtaleObjects (D.obj i) ∧ Nonempty (W ⟶ (smallEtaleBaseChange (c.π.app i)).obj V₀)}

section Stage

variable [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
  (hc : IsLimit c) (G : EtaleSheafSystem D Ab.{u + 1}) [∀ i, Injective (G.obj i)]
  {𝓖 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
  (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (G.obj i) ⟶ 𝓖)
  (hι : LimitHigherDirectImage.IsPullbackCocone c G ι)
  (hpres : LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓖 G ι)

include hc hι hpres in
/-- **The Čech cohomology of the colimit of a system of injective sheaves vanishes along the base
change of a family of a stage** in positive degrees, as soon as the iterated fibre products of
the family are quasi-compact and quasi-separated. The Čech complex is that of the direct image
to the stage, which is elementwise the colimit of the Čech complexes of the direct images of the
injective sheaves of the system (the degree zero case of Stacks 09YQ). -/
theorem isZero_cechCohomology_map_of_injective {i₀ : Iᵒᵖ} {U₀ : (D.obj i₀).Etale}
    (E₀ : PreZeroHypercover.{u} U₀) [Finite E₀.I₀]
    (hfib : ∀ (n : ℕ) (t : Fin (n + 1) → E₀.I₀),
      CompactSpace ((∏ᶜ fun a ↦ Over.mk (E₀.f (t a))) : Over U₀).left.left ∧
        QuasiSeparatedSpace ((∏ᶜ fun a ↦ Over.mk (E₀.f (t a))) : Over U₀).left.left)
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology (E₀.map (smallEtaleBaseChange (c.π.app i₀))) 𝓖.obj p) := by
  refine IsZero.of_iso ?_ (cechCohomologyIsoOfFunctor (smallEtaleBaseChange (c.π.app i₀)) E₀
    𝓖.obj (isIso_cechProductMapOfFunctor_smallEtaleBaseChange _ E₀) p)
  let Λ := {k : I // i₀.unop ≤ k}
  let a : ∀ k : Λ, Opposite.op k.1 ⟶ i₀ := fun k ↦ (homOfLE k.2).op
  let Pk : Λ → (D.obj i₀).Etaleᵒᵖ ⥤ Ab.{u + 1} := fun k ↦
    ((systemPushforward D Ab.{u + 1} (a k)).obj (G.obj (Opposite.op k.1))).obj
  let φ : ∀ k, Pk k ⟶ ((smallEtalePushforwardAb (c.π.app i₀)).obj 𝓖).obj := fun k ↦
    (G.pushforwardLeg c ι (a k)).hom
  let ψ : ∀ {k l : Λ}, k ≤ l → (Pk k ⟶ Pk l) := fun {k l} h ↦
    (G.pushforwardTransition (homOfLE (show k.1 ≤ l.1 from h)).op (a k)).hom
  have : Nonempty Λ := ⟨⟨i₀.unop, le_rfl⟩⟩
  have : IsDirected Λ (· ≤ ·) := ⟨fun k l ↦ by
    obtain ⟨m, hkm, hlm⟩ := directed_of (· ≤ ·) k.1 l.1
    exact ⟨⟨m, k.2.trans hkm⟩, hkm, hlm⟩⟩
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  refine exactAt_cechComplex_of_forall_exists E₀ φ ψ (fun {k l} h ↦ ?_) (fun {k l m} h₁ h₂ ↦ ?_)
    (fun n t x ↦ ?_) (fun n t k y hy ↦ ?_) p (fun k ↦ ?_)
  · exact congrArg (fun f ↦ f.hom)
      (G.pushforwardTransition_comp_pushforwardLeg c ι hι (homOfLE (show k.1 ≤ l.1 from h)).op
        (a k))
  · exact (congrArg (fun f ↦ f.hom) (G.pushforwardTransition_comp (homOfLE
      (show l.1 ≤ m.1 from h₂)).op (homOfLE (show k.1 ≤ l.1 from h₁)).op (a k))).symm
  · obtain ⟨hc₁, hc₂⟩ := hfib n t
    obtain ⟨k, b, y, hy⟩ := G.exists_pushforwardLeg_apply_eq c hc ι hι hpres _ x
    have hk : i₀.unop ≤ k.unop := leOfHom b.unop
    obtain rfl : b = (homOfLE hk).op := Subsingleton.elim _ _
    exact ⟨⟨k.unop, hk⟩, y, hy⟩
  · obtain ⟨hc₁, hc₂⟩ := hfib n t
    obtain ⟨l, b, hb⟩ := G.exists_pushforwardTransition_apply_eq_zero c hc ι hι hpres _ (a k) y hy
    have hkl : k.1 ≤ l.unop := leOfHom b.unop
    obtain rfl : b = (homOfLE hkl).op := Subsingleton.elim _ _
    exact ⟨⟨l.unop, k.2.trans hkl⟩, hkl, hb⟩
  · rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact isZero_cechCohomology_pushforward_of_injective (D.map (a k)) E₀
      (G.obj (Opposite.op k.1)) p hp

private theorem descent_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₃' : 𝒳}
    {exl : o₀ ⟶ o₁} {mapl : o₁ ⟶ o₂} {fst₁ : o₂ ⟶ o₃} {fstU : o₃ ⟶ o₄} {fst₂ : o₁ ⟶ o₅}
    {ψl : o₅ ⟶ o₃} {θ : o₀ ⟶ o₅} {fl : o₀ ⟶ o₆} {eul : o₆ ⟶ o₇} {fsti : o₇ ⟶ o₄}
    {cpl : o₇ ⟶ o₈} {fst₁' : o₈ ⟶ o₃'} {fstU' : o₃' ⟶ o₄}
    (h₁ : mapl ≫ fst₁ = fst₂ ≫ ψl) (h₂ : exl ≫ fst₂ = θ)
    (h₃ : θ ≫ ψl ≫ fstU = (fl ≫ eul) ≫ fsti) (h₄ : cpl ≫ fst₁' ≫ fstU' = fsti) :
    (exl ≫ mapl) ≫ fst₁ ≫ fstU = (fl ≫ eul ≫ cpl) ≫ fst₁' ≫ fstU' := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃, h₄, Category.assoc]

include hc hι hpres in
/-- **The Čech cohomology of the colimit of a system of injective sheaves vanishes** in positive
degrees, along a finite family of objects with affine underlying schemes covering an object `U`
with quasi-compact and quasi-separated underlying scheme which lies over the base change of a
quasi-compact and quasi-separated object `V₁` of a stage. The family descends to a stage,
together with `U`, and its Čech complex is that of the descended family,
`isZero_cechCohomology_map_of_injective`. -/
theorem isZero_cechCohomology_of_injective {U : c.pt.Etale} (hU : U ∈ qcqsEtaleObjects c.pt)
    {i₁ : Iᵒᵖ} (V₁ : (D.obj i₁).Etale) [CompactSpace V₁.left] [QuasiSeparatedSpace V₁.left]
    (gU : U ⟶ (smallEtaleBaseChange (c.π.app i₁)).obj V₁)
    (E : PreZeroHypercover.{u} U) [Finite E.I₀] (haff : ∀ a, IsAffine (E.X a).left)
    (p : ℕ) (hp : 0 < p) : IsZero (cechCohomology E 𝓖.obj p) := by
  obtain ⟨hUc, hUs⟩ := hU
  have : Etale U.hom := U.prop
  have : Etale V₁.hom := V₁.prop
  have : CompactSpace ((𝟭 Scheme.{u}).obj U.left) := hUc
  have : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj U.left) := hUs
  have : CompactSpace ((𝟭 Scheme.{u}).obj V₁.left) := inferInstanceAs (CompactSpace V₁.left)
  have : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj V₁.left) :=
    inferInstanceAs (QuasiSeparatedSpace V₁.left)
  obtain ⟨i, -, Y, pY, θ, hpY, hYc, hYs, hθ⟩ := exists_isPullback_etale_of_isLimit_of_hom D c hc
    V₁.hom U.hom (gU.left ≫ pullback.fst V₁.hom (c.π.app i₁))
    (smallEtaleBaseChange_left_fst_hom _ gU)
  have : Etale pY := hpY
  let U₀ : (D.obj i).Etale := Scheme.Etale.mk pY
  have : CompactSpace U₀.left := hYc
  have : QuasiSeparatedSpace U₀.left := hYs
  let eU : U ≅ (smallEtaleBaseChange (c.π.app i)).obj U₀ :=
    MorphismProperty.Comma.isoMk hθ.isoPullback (Iso.refl _)
      (by exact (hθ.isoPullback_hom_snd).trans (Category.comp_id _).symm)
  let gV : ∀ a, E.X a ⟶ (smallEtaleBaseChange (c.π.app i)).obj U₀ := fun a ↦ E.f a ≫ eU.hom
  choose j e hdesc using fun a ↦
    have := haff a; exists_stageDescent D c hc (E.X a) U₀ U₀ (gV a) (gV a)
  obtain ⟨m, hm⟩ := Finite.exists_le fun o : Option E.I₀ ↦ o.elim i.unop fun a ↦ (j a).unop
  let e' : Opposite.op m ⟶ i := (homOfLE (hm none)).op
  choose Z θa ψ χ hZc hZs hθa hψ hχ using fun a ↦
    (hdesc a).of_le (homOfLE (hm (some a))).op e' (Subsingleton.elim _ _)
  let Um : (D.obj (Opposite.op m)).Etale := (smallEtaleBaseChange (D.map e')).obj U₀
  let E₀ : PreZeroHypercover.{u} Um := { I₀ := E.I₀, X := Z, f := ψ }
  let u := smallEtaleBaseChange (c.π.app (Opposite.op m))
  let e₂ : U ≅ u.obj Um := eU ≪≫ (smallEtaleBaseChangeComp' (c.π.app (Opposite.op m)) (D.map e')
    (c.π.app i) (c.w e').symm).app U₀
  have : ∀ a, Etale (Z a).hom := fun a ↦ (Z a).prop
  let eX : ∀ a, E.X a ≅ u.obj (Z a) := fun a ↦
    MorphismProperty.Comma.isoMk (hθa a).isoPullback (Iso.refl _)
      (by exact ((hθa a).isoPullback_hom_snd).trans (Category.comp_id _).symm)
  have hw : ∀ a, (eX a).hom ≫ u.map (ψ a) = E.f a ≫ e₂.hom := fun a ↦
    smallEtaleBaseChange_baseChange_hom_ext (c.π.app (Opposite.op m)) (D.map e') <|
      descent_chain (smallEtaleBaseChange_map_left_fst (c.π.app (Opposite.op m)) (ψ a))
        ((hθa a).isoPullback_hom_fst) (hψ a)
        (smallEtaleBaseChangeComp'_fst_fst (c.π.app (Opposite.op m)) (D.map e') (c.π.app i)
          (c.w e').symm U₀)
  refine isZero_cechCohomology_of_iso E (fun a ↦ u.obj (Z a)) (fun a ↦ u.map (ψ a)) e₂ eX hw
    𝓖.obj p ?_
  have hUm : Um ∈ qcqsEtaleObjects (D.obj (Opposite.op m)) :=
    ⟨compactSpace_smallEtaleBaseChange_obj (D.map e') U₀ hYc,
      quasiSeparatedSpace_smallEtaleBaseChange_obj (D.map e') U₀ hYs⟩
  exact isZero_cechCohomology_map_of_injective hc G ι hι hpres E₀ (fun n t ↦
    compactSpace_and_quasiSeparatedSpace_pi_of_mem_qcqsEtaleObjects hUm (fun b ↦ ψ (t b))
      fun b ↦ ⟨hZc (t b), hZs (t b)⟩) p hp

include hc hι hpres in
/-- **The higher cohomology of the colimit of a system of injective sheaves vanishes over every
object of `Stacks.EtaleCohomology.qcqsOverStageObjects`** (the case `p > 0` of
[Stacks, Tag 09YQ] for a system of injective sheaves, over an object): `Ext^{q+1}` out of the free
abelian sheaf on such an object `U` into `𝓖 = colim f_i⁻¹𝒢_i` vanishes. The stages `X_i` are
arbitrary.

The coverings of such an object by finitely many objects with affine underlying schemes are
cofinal, and their iterated fibre products are again such objects; along them the Čech cohomology
of `𝓖` vanishes in positive degrees (`isZero_cechCohomology_of_injective`), so the higher
cohomology vanishes by [Stacks, Tag 03F9]. -/
theorem EtaleSheafSystem.subsingleton_ext_of_injective {U : c.pt.Etale}
    (hU : U ∈ qcqsOverStageObjects c) (q : ℕ) :
    Subsingleton (Abelian.Ext.{u + 1} ((presheafToSheaf (smallEtaleTopology c.pt) Ab.{u + 1}).obj
      (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free)) 𝓖 (q + 1)) := by
  let J := smallEtaleTopology c.pt
  let B := qcqsOverStageObjects c
  let Cov : ∀ U : c.pt.Etale, Set { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ J U } :=
    fun U E ↦ E.1 ∈ qcqsEtaleCovering c.pt U ∧ U ∈ B ∧ ∀ a, IsAffine (E.1.X a).left
  have hlift : ∀ {V W : c.pt.Etale}, W ∈ B → (V ⟶ W) → V ∈ qcqsEtaleObjects c.pt → V ∈ B :=
    fun {V W} hW g hV ↦ by
      obtain ⟨-, i, V₀, hV₀, ⟨gW⟩⟩ := hW
      exact ⟨hV, i, V₀, hV₀, ⟨g ≫ gW⟩⟩
  have hfib : ∀ {U : c.pt.Etale} (E : PreZeroHypercover.{u} U), E ∈ qcqsEtaleCovering c.pt U →
      ∀ (n : ℕ) (t : Fin (n + 1) → E.I₀),
        ((∏ᶜ fun a ↦ Over.mk (E.f (t a))) : Over U).left ∈ qcqsEtaleObjects c.pt := by
    intro U E hE n t
    obtain ⟨tc, ⟨htc⟩, hB⟩ := (hasIntersectionsIn_qcqsEtaleObjects U E hE).2.2.2 n t
    exact mem_qcqsEtaleObjects_of_iso (piOverLeftIsoOfIsLimit tc htc) hB
  exact Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero.{u + 1, u} J B Cov
    (fun E _ n t ↦ inferInstance)
    (fun {U} E hE ↦ ⟨hE.2.1, fun a ↦ hlift hE.2.1 (E.1.f a) (hE.1.2.2.1 a),
      fun n t ↦ hlift hE.2.1 ((∏ᶜ fun a ↦ Over.mk (E.1.f (t a))) : Over U).hom
        (hfib E.1 hE.1 n t)⟩)
    (fun U hU R hR ↦ by
      obtain ⟨E, hE, haff, hle⟩ := exists_qcqsCovering_le U hU.1 R hR
      exact ⟨⟨E, hE.2.2.2⟩, ⟨hE, hU, haff⟩, hle⟩)
    𝓖 (fun {U} E hE p hp ↦ by
      have : Finite E.1.I₀ := hE.1.1
      obtain ⟨-, i, V₀, hV₀, ⟨gU⟩⟩ := hE.2.1
      have := hV₀.1
      have := hV₀.2
      exact isZero_cechCohomology_of_injective hc G ι hι hpres hE.1.2.1 V₀ gU E.1 hE.2.2 p hp)
    U hU (q + 1) (Nat.succ_pos q)

include hc hι hpres in
/-- **The higher derived sections of the colimit of a system of injective sheaves vanish over
every object of `Stacks.EtaleCohomology.qcqsOverStageObjects`**: the right derived functors of
the sections over such an object `U` vanish in positive degrees on `𝓖 = colim f_i⁻¹𝒢_i`, the
`𝒢_i` being injective. The stages `X_i` are arbitrary. This is
`EtaleSheafSystem.subsingleton_ext_of_injective` read through the identification of `Ext` out of
the free abelian sheaf on `U` with the right derived functors of the sections over `U`. -/
theorem EtaleSheafSystem.isZero_rightDerived_sheafSections_of_injective {U : c.pt.Etale}
    (hU : U ∈ qcqsOverStageObjects c) (q : ℕ) :
    IsZero ((((sheafSections (smallEtaleTopology c.pt) Ab.{u + 1}).obj (op U)).rightDerived
      (q + 1)).obj 𝓖) := by
  obtain ⟨e⟩ :=
    Stacks.Cohomology.FreeYonedaUnivLE.nonempty_extFunctorObj_iso_rightDerived_sections.{0}
      (smallEtaleTopology c.pt) U (q + 1)
  exact (@AddCommGrpCat.isZero_of_subsingleton _
    (EtaleSheafSystem.subsingleton_ext_of_injective hc G ι hι hpres hU q)).of_iso (e.app 𝓖).symm

include hc hι hpres in
/-- **The higher cohomology of the colimit of a system of injective sheaves vanishes** (the case
`p > 0` of [Stacks, Tag 09YQ] for a system of injective sheaves). Let `X = lim X_i` be the limit
of a directed inverse system of quasi-compact and quasi-separated schemes with affine transition
morphisms, and let `𝒢 = colim f_i⁻¹𝒢_i` with every `𝒢_i` injective. Then `H^{q+1}(X, 𝒢) = 0`.

The final object of the small étale site of `X` is the base change of the final object of the
small étale site of any stage, which is quasi-compact and quasi-separated; this is the case of
the final object of `EtaleSheafSystem.subsingleton_ext_of_injective`. -/
theorem EtaleSheafSystem.subsingleton_H_of_injective [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} 𝓖 (q + 1)) := by
  have hXc : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  obtain ⟨i⟩ : Nonempty Iᵒᵖ := inferInstance
  have hXs : QuasiSeparatedSpace c.pt := by
    have := isAffineHom_π_app D c hc i
    exact quasiSeparatedSpace_of_quasiSeparated (c.π.app i)
  let V₀ : (D.obj i).Etale := Scheme.Etale.mk (𝟙 (D.obj i))
  have hV₀ : V₀ ∈ qcqsEtaleObjects (D.obj i) :=
    ⟨inferInstanceAs (CompactSpace (D.obj i)), inferInstanceAs (QuasiSeparatedSpace (D.obj i))⟩
  have hT : Scheme.Etale.mk (𝟙 c.pt) ∈ qcqsOverStageObjects c :=
    ⟨⟨inferInstanceAs (CompactSpace c.pt), inferInstanceAs (QuasiSeparatedSpace c.pt)⟩, i, V₀,
      hV₀, ⟨smallEtaleBaseChangeHomMk (c.π.app i) (U := Scheme.Etale.mk (𝟙 c.pt)) (W := V₀)
        (c.π.app i) (show c.π.app i ≫ 𝟙 _ = 𝟙 _ ≫ c.π.app i by simp)⟩⟩
  have hsub := EtaleSheafSystem.subsingleton_ext_of_injective hc G ι hι hpres hT q
  have he : IsTerminal (Scheme.Etale.mk (𝟙 c.pt)) := by
    have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
      ⟨fun _ ↦ inferInstance⟩
    exact MorphismProperty.Over.mkIdTerminal _ _
  exact (((Abelian.extFunctor (q + 1)).mapIso
    (Stacks.CechSite.freeSheafIsoConstantSheaf (smallEtaleTopology c.pt) he).op).app
      𝓖).addCommGroupIsoToAddEquiv.subsingleton_congr.mpr hsub

end Stage

end Stacks.EtaleCohomology
