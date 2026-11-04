module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthTwo
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.IdealPowerDirectSum
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionConstruction
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.NestedImprovementComposition
public import StacksFrontier.Algebra.Module.DepthSubsingleton

/-!
# The depth-two improvement of a coherent formal module along a specialization-stable subset

Let `X` be a Noetherian scheme which locally has a dualizing complex, let `ℐ` be a
quasi-coherent ideal sheaf with support `Y`, let `T' ⊆ T ⊆ Y` be stable under specialization and
let `(ℱₙ)` be an object of `Coh(X, ℐ)`. Assume that every immediate specialization `y ⤳ y'` of
points of `Y` with `y' ∈ T'` has `y ∈ T` (condition (e) of [Stacks, Tag 0EJF]).

This file carries out the construction in the first paragraph of the source's proof. Dividing
out the sections supported on `T` gives the system `(ℱ'ₙ)` of [Stacks, Tag 0EJE]; each `ℱ'ₙ`
admits a depth-two extension `ℱ'ₙ ⟶ ℱ''ₙ` along `T'` ([Stacks, Tag 0EI3]), because at an
immediate specialization `y ⤳ y'` into `T'` from outside `T'` either `y` lies off `Y`, where
`ℱ'ₙ` has vanishing stalk, or `y ∈ T` by condition (e), where `ℱ'ₙ` has depth at least one.
The extensions are chosen as stabilized open extensions, which makes each of them universal
among maps into coherent modules of depth at least two along `T'`; that universality supplies
the transition maps of `(ℱ''ₙ)` and the canonical map `(ℱₙ) ⟶ (ℱ''ₙ)`.

## Main definitions

* `Stacks.Algebraization.canonicalDepthTwoImprovement`: the termwise depth-two extensions of
  `(ℱ'ₙ)` along `T'`, constructed from the hypotheses.
* `Stacks.Algebraization.universalImprovedSystem`: the inverse system `(ℱ''ₙ)` attached to
  termwise depth-two extensions which are universal.
* `Stacks.Algebraization.toUniversalImprovedSystem`: the canonical map `(ℱₙ) ⟶ (ℱ''ₙ)`.

## Main results

* `Stacks.Algebraization.bijective_precomp_of_isStabilizedOpenExtension`: a stabilized
  depth-two extension along any subset is universal among maps into coherent modules of depth at
  least two along that subset.
* `Stacks.Algebraization.isNestedImprovement_toUniversalImprovedSystem_app`: each component of
  the canonical map is an improvement along `T' ⊆ T` in the sense of [Stacks, Tag 0EI4].
* `Stacks.Algebraization.depth_stalk_canonicalImprovedSystem`: conclusions (1) and (2) of
  [Stacks, Tag 0EJF] for the constructed system.

## Implementation notes

Universality along a subset that need not be closed is reduced to universality along a closed
one. A stabilized open extension `ψ` along `T'` comes with an open `V` whose complement lies in
`T'` and on whose points `ψ` is an isomorphism of stalks; the complement `Z` of `V` is closed,
`ψ` is a depth-two extension along `Z`, and every module of depth at least two along `T'` has
depth at least two along `Z`. So
`Stacks.Algebraization.bijective_precomp_of_isDepthTwoExtension`, which is stated for a closed
subset, applies with `Z` in place of `T'`.

## References

* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE)
* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
* [Stacks Project, Tag 0EI4](https://stacks.math.columbia.edu/tag/0EI4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization

/-! ### Universality of a stabilized depth-two extension -/

/-- **A stabilized depth-two extension is universal.** Let `φ : ℱ ⟶ 𝒢` be a depth-two extension
along a subset `T'` which is also a stabilized open extension along `T'`, and let `𝒦` be a
coherent module whose stalks have depth at least two at the points of `T'`. Then every map
`ℱ ⟶ 𝒦` factors uniquely through `φ`. -/
public theorem bijective_precomp_of_isStabilizedOpenExtension {X : Scheme.{u}} [IsNoetherian X]
    {T' : Set X} {F G : X.Modules} (φ : F ⟶ G) (hφ : IsDepthTwoExtension T' φ)
    (hstab : IsStabilizedOpenExtension T' φ) (K : X.Modules) [K.IsCoherent]
    (hK : ∀ x : X, x ∈ T' →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) K.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) K.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) K.val.presheaf x)) :
    Function.Bijective fun l : G ⟶ K => φ ≫ l := by
  obtain ⟨V, hVT, hiso⟩ : ∃ V : X.Opens, ((V : Set X)ᶜ ⊆ T') ∧
      ∀ y : X, y ∈ (V : Set X) →
        IsIso (AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf y φ) := by
    by_cases hX : Nonempty X
    · obtain ⟨x⟩ := hX
      obtain ⟨V, hVT, -, hiso, -⟩ := hstab.2 x
      exact ⟨V, hVT, hiso⟩
    · refine ⟨⊤, fun y _ => (hX ⟨y⟩).elim, fun y _ => (hX ⟨y⟩).elim⟩
  exact bijective_precomp_of_isDepthTwoExtension V.isOpen.isClosed_compl φ
    ⟨hφ.1, fun y hy => hiso y (not_not.mp hy), fun y hy => hφ.2.2 y (hVT hy)⟩ K
    fun y hy => hK y (hVT hy)

/-! ### The inverse system of universal depth-two extensions -/

section System

variable {X : Scheme.{u}} [IsNoetherian X] {T T' : Set X}
  {hT : StableUnderSpecialization T} {F : ℕᵒᵖ ⥤ X.Modules}
  [∀ n : ℕᵒᵖ, (F.obj n).IsCoherent]

/-- Termwise depth-two extensions of `(ℱ'ₙ)` are *universal* when precomposition with the
extension at `m` is a bijection onto the maps from `ℱ'ₘ` into the extension at `n`, for all
`m` and `n`. -/
public def DepthTwoImprovement.IsUniversal (S : DepthTwoImprovement T T' hT F) : Prop :=
  ∀ m n : ℕᵒᵖ, Function.Bijective fun l : S.term m ⟶ S.term n => S.extend m ≫ l

/-- The transition map `ℱ''ₘ ⟶ ℱ''ₙ` induced by a transition map `ℱₘ ⟶ ℱₙ`, obtained from the
universal property of the depth-two extension at `m`. -/
public def universalImprovedMap {S : DepthTwoImprovement T T' hT F} (hS : S.IsUniversal)
    {m n : ℕᵒᵖ} (f : m ⟶ n) : S.term m ⟶ S.term n :=
  (Equiv.ofBijective _ (hS m n)).symm ((improvedSystem T hT F).map f ≫ S.extend n)

/-- The induced transition map is compatible with the extension maps. -/
public theorem extend_comp_universalImprovedMap {S : DepthTwoImprovement T T' hT F}
    (hS : S.IsUniversal) {m n : ℕᵒᵖ} (f : m ⟶ n) :
    S.extend m ≫ universalImprovedMap hS f = (improvedSystem T hT F).map f ≫ S.extend n :=
  (Equiv.ofBijective _ (hS m n)).apply_symm_apply _

/-- The inverse system `(ℱ''ₙ)` of universal depth-two extensions of `(ℱ'ₙ)`. -/
public def universalImprovedSystem {S : DepthTwoImprovement T T' hT F} (hS : S.IsUniversal) :
    ℕᵒᵖ ⥤ X.Modules where
  obj n := S.term n
  map f := universalImprovedMap hS f
  map_id n := by
    refine (hS n n).1 ?_
    change S.extend n ≫ universalImprovedMap hS (𝟙 n) = S.extend n ≫ 𝟙 _
    rw [extend_comp_universalImprovedMap, (improvedSystem T hT F).map_id, Category.id_comp,
      Category.comp_id]
  map_comp {l m n} f g := by
    refine (hS l n).1 ?_
    change S.extend l ≫ universalImprovedMap hS (f ≫ g) =
      S.extend l ≫ (universalImprovedMap hS f ≫ universalImprovedMap hS g)
    rw [extend_comp_universalImprovedMap, (improvedSystem T hT F).map_comp, Category.assoc,
      ← Category.assoc (S.extend l), extend_comp_universalImprovedMap, Category.assoc,
      extend_comp_universalImprovedMap]

/-- The term of `universalImprovedSystem hS` at `n` is the depth-two extension `S.term n`. -/
@[simp]
public theorem universalImprovedSystem_obj {S : DepthTwoImprovement T T' hT F}
    (hS : S.IsUniversal) (n : ℕᵒᵖ) : (universalImprovedSystem hS).obj n = S.term n :=
  rfl

/-- The transition map of `universalImprovedSystem hS` along `f` is
`universalImprovedMap hS f`. -/
@[simp]
public theorem universalImprovedSystem_map {S : DepthTwoImprovement T T' hT F}
    (hS : S.IsUniversal) {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (universalImprovedSystem hS).map f = universalImprovedMap hS f :=
  rfl

/-- The canonical map `(ℱₙ) ⟶ (ℱ''ₙ)`: the depth-one quotient map followed by the depth-two
extension. -/
public def toUniversalImprovedSystem {S : DepthTwoImprovement T T' hT F} (hS : S.IsUniversal) :
    F ⟶ universalImprovedSystem hS where
  app n := (toImprovedSystem T hT F).app n ≫ S.extend n
  naturality m n f := by
    change F.map f ≫ ((toImprovedSystem T hT F).app n ≫ S.extend n) =
      ((toImprovedSystem T hT F).app m ≫ S.extend m) ≫ universalImprovedMap hS f
    rw [Category.assoc, extend_comp_universalImprovedMap, ← Category.assoc,
      (toImprovedSystem T hT F).naturality f, Category.assoc]

/-- The component of `toUniversalImprovedSystem hS` at `n` is the depth-one quotient map at `n`
followed by the depth-two extension `S.extend n`. -/
@[simp]
public theorem toUniversalImprovedSystem_app {S : DepthTwoImprovement T T' hT F}
    (hS : S.IsUniversal) (n : ℕᵒᵖ) :
    (toUniversalImprovedSystem hS).app n = (toImprovedSystem T hT F).app n ≫ S.extend n :=
  rfl

/-- Each component of the canonical map is an improvement of `ℱₙ` along `T' ⊆ T` in the sense
of [Stacks, Tag 0EI4]: the depth-one quotient along `T` followed by a depth-two extension along
`T'`. In particular it is determined up to unique isomorphism by
`AlgebraicGeometry.nestedImprovement_unique`. -/
public theorem isNestedImprovement_toUniversalImprovedSystem_app (hTT' : T' ⊆ T)
    {S : DepthTwoImprovement T T' hT F} (hS : S.IsUniversal) (n : ℕᵒᵖ) :
    IsNestedImprovement T T' ((toUniversalImprovedSystem hS).app n) :=
  isNestedImprovement_depthOneQuotient_comp X T T' hTT' hT (F.obj n) (S.extend n)
    (S.extend_isDepthTwoExtension n)

end System

/-! ### The construction from the hypotheses of the source -/

section Construction

variable {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}

/-- The terms of a coherent adic system are coherent. -/
public instance coherentAdicSystems_obj_isCoherent (F : Stacks.Coherent.CoherentAdicSystems I)
    (n : ℕᵒᵖ) : (F.obj.obj n).IsCoherent :=
  F.property.1 n.unop

/-- Off the support of `ℐ` the stalks of the depth-one quotients of a coherent adic system
vanish, so they have infinite depth there. -/
theorem depth_improvedSystem_stalk_eq_top_of_notMem_support
    (F : Stacks.Coherent.CoherentAdicSystems I) (T : Set X) (hT : StableUnderSpecialization T)
    (hTY : T ⊆ I.support) (n : ℕᵒᵖ) (x : X) (hx : x ∉ I.support) :
    Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (((improvedSystem T hT F.obj).obj n).presheaf.stalk x) = ⊤ := by
  have hxT : x ∉ T := fun h => hx (hTY h)
  have hiso : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      ((toImprovedSystem T hT F.obj).app n).mapPresheaf) :=
    (isDepthOneQuotient_toImprovedSystem_app T hT F.obj n).2.2.1 x hxT
  have hsurj : Function.Surjective ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      ((toImprovedSystem T hT F.obj).app n).mapPresheaf) :=
    ((ConcreteCategory.isIso_iff_bijective _).1 hiso).2
  have hsub : Subsingleton (((improvedSystem T hT F.obj).obj n).presheaf.stalk x) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    have h0 : ∀ w : (F.obj.obj n).presheaf.stalk x, w = 0 := fun w =>
      eq_zero_stalk_of_notMem_support F hx n.unop w
    rw [h0 a', h0 b']
  exact Module.depth_eq_top_of_subsingleton _

/-- At an immediate specialization `x ⤳ x'` with `x' ∈ T'` and `x ∉ T'`, the depth-one quotient
of `ℱₙ` along `T` has depth at least one at `x`: either `x ∉ Y`, where its stalk vanishes, or
`x ∈ Y`, and then `x ∈ T` by condition (e). -/
theorem one_le_depth_improvedSystem_stalk_of_isImmediateSpecialization
    (F : Stacks.Coherent.CoherentAdicSystems I) {T T' : Set X}
    (hT : StableUnderSpecialization T) (hTY : T ⊆ I.support)
    (himm : ∀ x x' : X, x ∈ I.support → IsImmediateSpecialization x x' → x' ∈ T' → x ∈ T)
    (n : ℕᵒᵖ) (x x' : X) (hxx' : IsImmediateSpecialization x x') (hx' : x' ∈ T') :
    (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (((improvedSystem T hT F.obj).obj n).presheaf.stalk x) := by
  by_cases hxY : x ∈ I.support
  · exact one_le_depth_improvedSystem_stalk T hT F.obj n x (himm x x' hxY hxx' hx')
  · rw [depth_improvedSystem_stalk_eq_top_of_notMem_support F T hT hTY n x hxY]
    exact le_top

/-- **The termwise depth-two extensions exist.** Under the hypotheses of [Stacks, Tag 0EJF]
relevant to the construction, each depth-one quotient `ℱ'ₙ` has a depth-two extension along `T'`
which is moreover a stabilized open extension along `T'`. -/
public theorem exists_stabilized_depthTwoExtension_improvedSystem
    (hdual : HasDualizingComplexOnAffineCover X) (F : Stacks.Coherent.CoherentAdicSystems I)
    {T T' : Set X} (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
    (hTY : T ⊆ I.support)
    (himm : ∀ x x' : X, x ∈ I.support → IsImmediateSpecialization x x' → x' ∈ T' → x ∈ T)
    (n : ℕᵒᵖ) :
    ∃ (G : X.Modules) (ψ : (improvedSystem T hT F.obj).obj n ⟶ G),
      IsDepthTwoExtension T' ψ ∧ IsStabilizedOpenExtension T' ψ := by
  have : ((improvedSystem T hT F.obj).obj n).IsCoherent :=
    (isDepthOneQuotient_toImprovedSystem_app T hT F.obj n).1
  have himm' : ∀ x x' : X, IsImmediateSpecialization x x' → x' ∈ T' → x ∉ T' →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (((improvedSystem T hT F.obj).obj n).presheaf.stalk x) :=
    fun x x' hxx' hx' _ =>
      one_le_depth_improvedSystem_stalk_of_isImmediateSpecialization F hT hTY himm n x x'
        hxx' hx'
  obtain ⟨Z, hZclosed, hZT, hBZ⟩ :=
    hasClosedLowDepthLocus_of_hasDualizingComplex X hdual T' hT' _ himm'
  exact exists_isDepthTwoExtension_of_isClosed X
    (isUniversallyCatenary_of_hasDualizingComplexOnAffineCover X hdual)
    (fun z => formalFibersHavePropertySk_stalk_of_hasDualizingComplexOnAffineCover X hdual z 1)
    T' hT' _ Z hZclosed hZT
    (fun x hx hxZ => by
      by_contra hc
      exact hxZ (hBZ ⟨hx, hc⟩))
    himm'

variable (hdual : HasDualizingComplexOnAffineCover X) (F : Stacks.Coherent.CoherentAdicSystems I)
  {T T' : Set X} (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
  (hTY : T ⊆ I.support)
  (himm : ∀ x x' : X, x ∈ I.support → IsImmediateSpecialization x x' → x' ∈ T' → x ∈ T)

/-- **The canonical termwise depth-two extensions** of the depth-one quotients `(ℱ'ₙ)` of a
coherent formal module along `T'`, constructed from the hypotheses of [Stacks, Tag 0EJF]. -/
public def canonicalDepthTwoImprovement : DepthTwoImprovement T T' hT F.obj where
  term n := (exists_stabilized_depthTwoExtension_improvedSystem hdual F hT hT' hTY himm n).choose
  extend n :=
    (exists_stabilized_depthTwoExtension_improvedSystem hdual F hT hT' hTY himm
      n).choose_spec.choose
  extend_isDepthTwoExtension n :=
    (exists_stabilized_depthTwoExtension_improvedSystem hdual F hT hT' hTY himm
      n).choose_spec.choose_spec.1

/-- The canonical termwise depth-two extensions are stabilized open extensions along `T'`. -/
public theorem isStabilizedOpenExtension_canonicalDepthTwoImprovement (n : ℕᵒᵖ) :
    IsStabilizedOpenExtension T'
      ((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend n) :=
  (exists_stabilized_depthTwoExtension_improvedSystem hdual F hT hT' hTY himm
    n).choose_spec.choose_spec.2

/-- The canonical termwise depth-two extensions are universal. -/
public theorem isUniversal_canonicalDepthTwoImprovement :
    (canonicalDepthTwoImprovement hdual F hT hT' hTY himm).IsUniversal := fun m n => by
  have h := (canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend_isDepthTwoExtension
  have := (h n).1
  exact bijective_precomp_of_isStabilizedOpenExtension _ (h m)
    (isStabilizedOpenExtension_canonicalDepthTwoImprovement hdual F hT hT' hTY himm m) _ (h n).2.2

/-- The inverse system `(ℱ''ₙ)` of [Stacks, Tag 0EJF]. -/
public abbrev canonicalImprovedSystem : ℕᵒᵖ ⥤ X.Modules :=
  universalImprovedSystem (isUniversal_canonicalDepthTwoImprovement hdual F hT hT' hTY himm)

/-- The canonical map `(ℱₙ) ⟶ (ℱ''ₙ)` of [Stacks, Tag 0EJF]. -/
public abbrev toCanonicalImprovedSystem : F.obj ⟶ canonicalImprovedSystem hdual F hT hT' hTY himm :=
  toUniversalImprovedSystem (isUniversal_canonicalDepthTwoImprovement hdual F hT hT' hTY himm)

/-- The terms of the improved system are coherent. -/
public theorem isCoherent_canonicalImprovedSystem_obj (n : ℕᵒᵖ) :
    ((canonicalImprovedSystem hdual F hT hT' hTY himm).obj n).IsCoherent :=
  ((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend_isDepthTwoExtension n).1

/-- **Conclusions (1) and (2) of [Stacks, Tag 0EJF].** Every term of `(ℱ''ₙ)` has depth at least
one at each point of `T` and depth at least two at each point of `T'`. -/
public theorem depth_stalk_canonicalImprovedSystem (n : ℕᵒᵖ) (x : X) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((canonicalImprovedSystem hdual F hT hT' hTY himm).obj n).val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) ((canonicalImprovedSystem hdual F hT hT' hTY himm).obj n).val x
    (x ∈ T → (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((canonicalImprovedSystem hdual F hT hT' hTY himm).obj n).val.presheaf x)) ∧
      (x ∈ T' → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((canonicalImprovedSystem hdual F hT hT' hTY himm).obj n).val.presheaf x)) :=
  depth_stalk_depthTwoImprovedSystem (canonicalDepthTwoImprovement hdual F hT hT' hTY himm) n x

end Construction

end Stacks.Algebraization

end
