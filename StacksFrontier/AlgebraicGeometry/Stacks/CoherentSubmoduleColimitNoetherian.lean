module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ChartFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ComoduleQuasicoherentHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentFilteredColimitOfMonos

/-!
# Every quasi-coherent module on a Noetherian algebraic stack is the filtered colimit of its
coherent submodules (Stacks 0GRF)

Let `𝒳` be a Noetherian algebraic stack (Stacks 0510).  Stacks 0GRF asserts that every
quasi-coherent `𝒪_𝒳`-module `ℱ` is the filtered colimit of its coherent submodules.

## The statement

"Submodule" is read in `QCoh(𝒪_𝒳)`, the category the statement lives in: a coherent submodule of
`ℱ` is a subobject of `ℱ` in `QCoh(𝒪_𝒳)` (an abelian category, Stacks 06WV (2)) whose underlying
module is coherent (Stacks 0GR6, `AlgebraicGeometry.Stack.IsCoherent`).  These form the partially
ordered type `AlgebraicGeometry.Stack.AlgebraicStacks.CoherentSubobject ℱ`; the theorem says that
it is filtered (nonempty and directed) and that `ℱ`, with the inclusions, is the colimit in
`QCoh(𝒪_𝒳)` of the diagram of their underlying modules.

The reading of "submodule" as a subsheaf in `Mod(𝒪_𝒳)` (a monomorphism of sheaves of modules on
the big fppf site, i.e. `𝒢(T) ⊆ ℱ(T)` for every object `T`) makes the statement false.  Take
`𝒳 = 𝔸¹_k = Spec k[x]` and `ℱ` the quasi-coherent module of `k[x, x⁻¹]`.  If `𝒢 ⊆ ℱ` is a
coherent subsheaf with `M = 𝒢(𝔸¹) ≠ 0`, then `M` is a nonzero finitely generated submodule of the
torsion-free `k[x, x⁻¹]`, hence free of positive rank, so `𝒢(Spec k[x]/(x)) = M/xM ≠ 0`, while
`ℱ(Spec k[x]/(x)) = k[x, x⁻¹]/x = 0`.  So the only coherent subsheaf of `ℱ` is `0`, and `ℱ ≠ 0`
is not their colimit.  A subobject in `QCoh(𝒪_𝒳)` need not be a subsheaf on the big site (its
sections need only inject over flat objects; base change along `Spec k[x]/(x) → 𝔸¹` is not
exact), and with that reading the statement holds: `k[x]·x⁻ⁿ` are coherent subobjects of `ℱ`.
The source works in `QCoh(𝒪_𝒳)` throughout: the image of `𝒢 ⊕ ℋ → ℱ` in its proof is taken there,
and for a scheme it is the classical notion (quasi-coherent submodules on the small Zariski site).

## The proof

The source reduces to a groupoid presentation `𝒳 = [U/R]` through Stacks 0GRC and quotes
Stacks 0GPS.  The equivalence `QCoh(𝒪_𝒳) ≅ QCoh(U, R, s, t, c)` is not available here, and the
argument runs on `𝒳` directly, along the same lines.  Let `a : (Sch/U) ⟶ 𝒳` be a smooth surjective
chart with `U` affine (Stacks 04YC), so `Γ(U)` is Noetherian (Stacks 04YF), and `u = a(id_U)`.

* A quasi-coherent module is coherent as soon as its sections over `u` are finitely generated
  (`AlgebraicGeometry.Stack.AlgebraicStacks.isCoherent_of_fg_chart`); so quotients and images of
  coherent modules in `QCoh(𝒪_𝒳)` are coherent, and the coherent subobjects are directed (the
  image of `𝒢 ⊕ ℋ → ℱ`, as in the source).
* Every section `f` of `ℱ` over `u` lies in a coherent subobject: quasi-separatedness of `𝒳` gives
  a universal pair `w ⇉ u` over an affine scheme (the affine objects of `u ×_𝒳 u`), `pr₁^*f` is a
  finite combination of `pr₂^*mᵢ`, and for `H = ⟨mᵢ⟩` the sections of `ℱ ∩ u_*H` contain `f` and
  lie in `H` (this is the module `ℱ ∩ s_*t^*ℋ` of Stacks 0GPS).  Its restriction to the flat-fppf
  site is quasi-coherent, `g_!` of it is a quasi-coherent module mapping onto it over `u`, and its
  image in `ℱ` is the coherent subobject sought
  (`AlgebraicGeometry.Stack.AlgebraicStacks.exists_quasicoherent_hom_range_eq_comoduleSubmodule`).
* A filtered system of subobjects whose sections over `u` exhaust those of `ℱ` has `ℱ` as its
  colimit (`AlgebraicGeometry.Stack.AlgebraicStacks.isColimit_of_mono_of_forall_mem_range`).

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.CoherentSubobject`
* `AlgebraicGeometry.Stack.AlgebraicStacks.coherentSubobjectDiagram`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.coherentSubobjectCocone`

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isFiltered_coherentSubobject_and_isColimit`:
  **Stacks 0GRF**.

## References

* [Stacks Project, Tag 0GRF](https://stacks.math.columbia.edu/tag/0GRF)
* [Stacks Project, Tag 0GRB](https://stacks.math.columbia.edu/tag/0GRB)
* [Stacks Project, Tag 0GRC](https://stacks.math.columbia.edu/tag/0GRC)
* [Stacks Project, Tag 0GPS](https://stacks.math.columbia.edu/tag/0GPS)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 075S](https://stacks.math.columbia.edu/tag/075S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.FibredSite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w w'

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat objModule

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

variable (B S hS 𝒳) in
/-- **The coherent submodules of a quasi-coherent module**: the subobjects of `ℱ` in
`QCoh(𝒪_𝒳)` whose underlying module is coherent (Stacks 0GR6), ordered by inclusion. -/
def CoherentSubobject (F : quasicoherentModules B S hS 𝒳) : Type (u + 1) :=
  {P : Subobject F // IsCoherent B S hS 𝒳 (Subobject.underlying.obj P).obj}

/-- The coherent submodules of `ℱ` are partially ordered by inclusion of subobjects. -/
instance (F : quasicoherentModules B S hS 𝒳) : PartialOrder (CoherentSubobject B S hS 𝒳 F) :=
  inferInstanceAs (PartialOrder {_P : Subobject F // _})

variable (B S hS 𝒳) in
/-- The diagram of the coherent submodules of `ℱ`. -/
def coherentSubobjectDiagram (F : quasicoherentModules B S hS 𝒳) :
    CoherentSubobject B S hS 𝒳 F ⥤ quasicoherentModules B S hS 𝒳 :=
  (Subtype.mono_coe _ : Monotone (Subtype.val : CoherentSubobject B S hS 𝒳 F → Subobject F)).functor
    ⋙ Subobject.underlying

variable (B S hS 𝒳) in
/-- The cocone of the inclusions of the coherent submodules of `ℱ`. -/
def coherentSubobjectCocone (F : quasicoherentModules B S hS 𝒳) :
    Cocone (coherentSubobjectDiagram B S hS 𝒳 F) where
  pt := F
  ι :=
    { app := fun P => P.1.arrow
      naturality := fun P Q h => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map]
        exact Subobject.underlying_arrow _ }

/-- **A Noetherian chart.**  A Noetherian algebraic stack has a smooth surjective chart
`a : (Sch/U) ⟶ 𝒳` with `U` affine (Stacks 04YC, quasi-compactness); `U` is locally Noetherian
(Stacks 04YF), so the ring of functions on `u = a(id_U)` is Noetherian. -/
theorem exists_noetherian_chart (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳) :
    ∃ (U : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U ⟶ 𝒳),
      AlgebraicStacks.IsSmooth B S hS a ∧ IsSurjective B S hS a ∧
        IsAffineOver B S hS (𝒳.val.val.p.obj (chartObject a)) ∧
          IsNoetherianRing (objRing B S hS 𝒳.val.val.p (chartObject a)) := by
  obtain ⟨U, hU, f, hsurj, hrel⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation B S hS 𝒳).1 h𝒳.1
  let a : schemeStack.{u, w} B S hS U ⟶ 𝒳 := f
  have hsm : AlgebraicStacks.IsSmooth B S hS a := isSmooth_of_isRelativelySmooth B S hS a hrel
  let : ObjectProperty.IsLocal (fun X : Scheme.{u} => IsLocallyNoetherian X)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  have hUn : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    (exists_scheme_atlas_iff_forall_scheme B S hS (fun X : Scheme.{u} => IsLocallyNoetherian X)
      𝒳).mp h𝒳.2.2 U a hsm
  have heq : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj (chartObject a)) =
      (BigFppfOver.toScheme B S hS).obj U :=
    congrArg (BigFppfOver.toScheme B S hS).obj (Functor.congr_obj a.hom.hom.w (Over.mk (𝟙 U)))
  refine ⟨U, a, hsm, hsurj, ?_, ?_⟩
  · change IsAffine _
    rw [heq]
    exact hU
  · change IsNoetherianRing
      Γ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj (chartObject a)), ⊤)
    rw [heq]
    exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

section Chart

variable {U : BigFppfOver B S hS} {a : schemeStack.{u, w} B S hS U ⟶ 𝒳}
  (hsm : AlgebraicStacks.IsSmooth B S hS a) (hsurj : IsSurjective B S hS a)
  (hu : IsAffineOver B S hS (𝒳.val.val.p.obj (chartObject a)))
  (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒳)
  [IsNoetherianRing (objRing B S hS 𝒳.val.val.p (chartObject a))]

/-- Equal composites of morphisms of `QCoh(𝒪_𝒳)` agree on sections. -/
private theorem app_apply_eq_of_comp_eq {P Q R : quasicoherentModules B S hS 𝒳}
    {f : P ⟶ Q} {g : Q ⟶ R} {h : P ⟶ R} (e : f ≫ g = h) (X) (y : P.obj.val.obj X) :
    g.hom.val.app X (f.hom.val.app X y) = h.hom.val.app X y := by
  subst e
  rfl

omit [IsNoetherianRing (objRing B S hS 𝒳.val.val.p (chartObject a))] in
include hu in
/-- The sections over the chart of a coherent module are finitely generated. -/
theorem fg_chart_of_isCoherent {M : quasicoherentModules B S hS 𝒳}
    (hM : IsCoherent B S hS 𝒳 M.obj) :
    Module.Finite (objRing B S hS 𝒳.val.val.p (chartObject a))
      (M.obj.val.obj (op (chartObject a))) := by
  have := finitePresentation_objRing_of_isFinitePresentationOnSite B S hS _ _ M.obj
    M.property hM.isFinitePresentationOnSite (chartObject a) hu
  exact instFiniteOfFinitePresentation _ _

include hsm hsurj hu h𝒳 in
/-- **A quotient in `QCoh(𝒪_𝒳)` of a coherent module is coherent.** -/
theorem isCoherent_of_epi {P Q : quasicoherentModules B S hS 𝒳} (π : P ⟶ Q) [Epi π]
    (hP : IsCoherent B S hS 𝒳 P.obj) : IsCoherent B S hS 𝒳 Q.obj := by
  have := preservesFiniteColimits_quasicoherentInclusion B S hS 𝒳
  have := preservesEpimorphisms_of_preservesColimitsOfShape (quasicoherentInclusion B S hS 𝒳)
  have : Epi ((quasicoherentInclusion B S hS 𝒳).map π) := inferInstance
  have hsur := surjective_app_of_epi 𝒳 P.property Q.property
    ((quasicoherentInclusion B S hS 𝒳).map π) hu
  have : Module.Finite ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf).obj.obj (op (chartObject a)))
      (P.obj.val.obj (op (chartObject a))) := fg_chart_of_isCoherent hu hP
  exact isCoherent_of_fg_chart hsm hsurj h𝒳 hu Q.property
    (Module.Finite.of_surjective (π.hom.val.app (op (chartObject a))).hom hsur)

include hsm hsurj hu h𝒳 in
/-- **A direct sum of two coherent modules is coherent**: its sections over the chart are
spanned by those of the summands. -/
theorem isCoherent_biprod {P Q : quasicoherentModules B S hS 𝒳}
    (hP : IsCoherent B S hS 𝒳 P.obj) (hQ : IsCoherent B S hS 𝒳 Q.obj) :
    IsCoherent B S hS 𝒳 (P ⊞ Q).obj := by
  let x := chartObject a
  let R' := (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids .fppf).obj.obj (op x)
  have : Module.Finite R' (P.obj.val.obj (op x)) := fg_chart_of_isCoherent hu hP
  have : Module.Finite R' (Q.obj.val.obj (op x)) := fg_chart_of_isCoherent hu hQ
  let i₁ := ((biprod.inl : P ⟶ P ⊞ Q).hom.val.app (op x)).hom
  let i₂ := ((biprod.inr : Q ⟶ P ⊞ Q).hom.val.app (op x)).hom
  have hsur : Function.Surjective (i₁.coprod i₂) := by
    intro z
    refine ⟨(((biprod.fst : P ⊞ Q ⟶ P).hom.val.app (op x)) z,
      ((biprod.snd : P ⊞ Q ⟶ Q).hom.val.app (op x)) z), ?_⟩
    have h := congrArg (fun g => g.hom.val.app (op x) z) (biprod.total (X := P) (Y := Q))
    simp only at h
    rw [LinearMap.coprod_apply]
    refine Eq.trans ?_ h
    rfl
  exact isCoherent_of_fg_chart hsm hsurj h𝒳 hu (P ⊞ Q).property
    (Module.Finite.of_surjective _ hsur)

include hsm hsurj hu h𝒳 in
/-- **The image in `QCoh(𝒪_𝒳)` of a map out of a coherent module is coherent.** -/
theorem isCoherent_imageSubobject {P F : quasicoherentModules B S hS 𝒳} (φ : P ⟶ F)
    (hP : IsCoherent B S hS 𝒳 P.obj) :
    IsCoherent B S hS 𝒳 (Subobject.underlying.obj (imageSubobject φ)).obj :=
  isCoherent_of_epi hsm hsurj hu h𝒳 (factorThruImageSubobject φ) hP

include hsm hsurj hu h𝒳 in
/-- **Every section of `ℱ` over the chart lies in a coherent submodule**, on a quasi-separated
algebraic stack.  The submodule is the image of a quasi-coherent module mapping onto
`ℱ ∩ u_*H` over `u`, for `H` generated by the coefficients of the coaction of the section. -/
theorem exists_coherentSubobject_mem_range (h𝒳qs : IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳)
    (F : quasicoherentModules B S hS 𝒳) (f : F.obj.val.obj (op (chartObject a))) :
    ∃ (Q : CoherentSubobject B S hS 𝒳 F)
      (y : (Subobject.underlying.obj Q.1).obj.val.obj (op (chartObject a))),
      Q.1.arrow.hom.val.app (op (chartObject a)) y = f := by
  let x := chartObject a
  have huflat : flatObject B S hS 𝒳.val x :=
    FlatFppf.flatObject_map B S hS a (AlgebraicStacks.isFlat_of_isSmooth B S hS a hsm)
      ⟨Over.mk (𝟙 U), flatObject_schemeStack_id.{u, w} B S hS U⟩
  obtain ⟨v, pr₁, pr₂, hv, hpr⟩ := exists_isUniversalPair_of_isQuasiSeparatedAbs h𝒳qs hu hu
  obtain ⟨H, hH, hf⟩ := exists_fg_mem_comoduleSubmodule F.property hu hv hpr f
  obtain ⟨P, φ, hrange, hinj⟩ :=
    exists_quasicoherent_hom_range_eq_comoduleSubmodule 𝒳 h𝒳qs F hu huflat H
  have hmem : ∀ y, φ.hom.val.app (op x) y ∈ H := fun y =>
    comoduleSubmodule_le F.obj H hu (by
      rw [← SetLike.mem_coe, ← hrange]
      exact ⟨y, rfl⟩)
  have : Module.Finite (objRing B S hS 𝒳.val.val.p x) H := Module.Finite.iff_fg.2 hH
  have : _root_.IsNoetherian (objRing B S hS 𝒳.val.val.p x) H :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  let g : P.obj.val.obj (op x) →ₗ[objRing B S hS 𝒳.val.val.p x] H :=
    { toFun := fun y => ⟨φ.hom.val.app (op x) y, hmem y⟩
      map_add' := fun y y' => Subtype.ext (map_add _ y y')
      map_smul' := fun c y => Subtype.ext ((φ.hom.val.app (op x)).hom.map_smul c y) }
  have hg : Function.Injective g := fun y y' h => hinj (congrArg Subtype.val h)
  have hP : IsCoherent B S hS 𝒳 P.obj :=
    isCoherent_of_fg_chart hsm hsurj h𝒳 hu P.property (Module.Finite.of_injective g hg)
  obtain ⟨y, hy⟩ : f ∈ Set.range (φ.hom.val.app (op x)) := by rwa [hrange]
  refine ⟨⟨imageSubobject φ, isCoherent_imageSubobject hsm hsurj hu h𝒳 φ hP⟩,
    (factorThruImageSubobject φ).hom.val.app (op x) y, ?_⟩
  rw [← hy]
  exact app_apply_eq_of_comp_eq (imageSubobject_arrow_comp φ) _ _

omit [IsNoetherianRing (objRing B S hS 𝒳.val.val.p (chartObject a))] in
include hsm hsurj hu in
/-- **Subobjects are compared on the sections over the chart.** -/
theorem le_of_forall_exists_eq {F : quasicoherentModules B S hS 𝒳} {P Q : Subobject F}
    (h : ∀ y : (Subobject.underlying.obj P).obj.val.obj (op (chartObject a)),
      ∃ z : (Subobject.underlying.obj Q).obj.val.obj (op (chartObject a)),
        Q.arrow.hom.val.app (op (chartObject a)) z = P.arrow.hom.val.app (op (chartObject a)) y) :
    P ≤ Q := by
  have h0 : P.arrow ≫ cokernel.π Q.arrow = 0 := by
    refine ObjectProperty.hom_ext _ (hom_eq_zero_of_chart hsm hsurj hu
      (Subobject.underlying.obj P).property _ fun y => ?_)
    obtain ⟨z, hz⟩ := h y
    have hc := congrArg (fun k => k.hom.val.app (op (chartObject a)) z)
      (cokernel.condition Q.arrow)
    change (cokernel.π Q.arrow).hom.val.app (op (chartObject a))
      (P.arrow.hom.val.app (op (chartObject a)) y) = 0
    rw [← hz]
    exact hc
  exact Subobject.le_of_comm (Abelian.monoLift Q.arrow P.arrow h0)
    (Abelian.monoLift_comp Q.arrow P.arrow h0)

end Chart

/-- **Stacks 0GRF.**  Let `𝒳` be a Noetherian algebraic stack.  Every quasi-coherent
`𝒪_𝒳`-module `ℱ` is the filtered colimit of its coherent submodules: the coherent subobjects of `ℱ`
in `QCoh(𝒪_𝒳)` form a filtered (nonempty and directed) partially ordered set, and `ℱ` with the
inclusions is the colimit in `QCoh(𝒪_𝒳)` of the diagram of their underlying modules.

"Submodule" means subobject in `QCoh(𝒪_𝒳)`, the category the source works in.  Read as subsheaves
of `ℱ` on the big fppf site the statement is false (`k[x, x⁻¹]` on `𝔸¹_k` has no nonzero coherent
subsheaf: it vanishes over `Spec k[x]/(x)`); see the module docstring. -/
@[stacks 0GRF]
theorem isFiltered_coherentSubobject_and_isColimit (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    (F : quasicoherentModules B S hS 𝒳) :
    IsFiltered (CoherentSubobject B S hS 𝒳 F) ∧
      Nonempty (IsColimit (coherentSubobjectCocone B S hS 𝒳 F)) := by
  obtain ⟨U, a, hsm, hsurj, hu, hN⟩ := exists_noetherian_chart h𝒳
  let x := chartObject a
  have hex := exists_coherentSubobject_mem_range hsm hsurj hu h𝒳.2.2 h𝒳.2.1 F
  -- directed
  have : IsDirectedOrder (CoherentSubobject B S hS 𝒳 F) := by
    refine ⟨fun A B' => ?_⟩
    let g := biprod.desc A.1.arrow B'.1.arrow
    refine ⟨⟨imageSubobject g, isCoherent_imageSubobject hsm hsurj hu h𝒳.2.2 g
      (isCoherent_biprod hsm hsurj hu h𝒳.2.2 A.2 B'.2)⟩, ?_, ?_⟩
    · exact Subobject.le_of_comm (biprod.inl ≫ factorThruImageSubobject g) (by simp [g])
    · exact Subobject.le_of_comm (biprod.inr ≫ factorThruImageSubobject g) (by simp [g])
  have : Nonempty (CoherentSubobject B S hS 𝒳 F) := ⟨(hex 0).choose⟩
  have : IsFiltered (CoherentSubobject B S hS 𝒳 F) := isFiltered_of_directed_le_nonempty _
  refine ⟨inferInstance, ⟨?_⟩⟩
  -- the coherent subobjects form a small set
  let T : CoherentSubobject B S hS 𝒳 F → Set (F.obj.val.obj (op x)) :=
    fun P => Set.range (P.1.arrow.hom.val.app (op x))
  have hle : ∀ {P Q : CoherentSubobject B S hS 𝒳 F}, T P = T Q → P.1 ≤ Q.1 := by
    intro P Q h
    refine le_of_forall_exists_eq hsm hsurj hu fun y => ?_
    have : P.1.arrow.hom.val.app (op x) y ∈ T Q := by
      rw [← h]
      exact ⟨y, rfl⟩
    exact this
  have : Small.{u} (CoherentSubobject B S hS 𝒳 F) :=
    small_of_injective fun P Q h => Subtype.ext (le_antisymm (hle h) (hle h.symm))
  have : EssentiallySmall.{u} (CoherentSubobject B S hS 𝒳 F) :=
    essentiallySmall_of_small_of_locallySmall _
  let e := equivSmallModel.{u} (CoherentSubobject B S hS 𝒳 F)
  have : IsFiltered (SmallModel.{u} (CoherentSubobject B S hS 𝒳 F)) := IsFiltered.of_equivalence e
  refine IsColimit.ofWhiskerEquivalence e.symm ?_
  have : ∀ j, Mono (((coherentSubobjectCocone B S hS 𝒳 F).whisker e.symm.functor).ι.app j) :=
    fun j => inferInstanceAs (Mono (e.inverse.obj j).1.arrow)
  refine isColimit_of_mono_of_forall_mem_range hsm hsurj hu
    ((coherentSubobjectCocone B S hS 𝒳 F).whisker e.symm.functor).ι fun f => ?_
  obtain ⟨Q, y, hy⟩ := hex f
  have hQ : Q.1 ≤ (e.inverse.obj (e.functor.obj Q)).1 := leOfHom (e.unitIso.hom.app Q)
  refine ⟨e.functor.obj Q, (Subobject.ofLE _ _ hQ).hom.val.app (op x) y, ?_⟩
  rw [← hy]
  exact app_apply_eq_of_comp_eq (Subobject.ofLE_arrow hQ) _ _

end AlgebraicGeometry.Stack.AlgebraicStacks

end
