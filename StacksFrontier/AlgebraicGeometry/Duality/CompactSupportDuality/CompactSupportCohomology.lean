module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactSupportDuality.Linearity
public import StacksFrontier.AlgebraicGeometry.Duality.CompactSupportDuality.ProDuality
public import
  StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.DegreeZeroCompactSupport
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLeray

/-!
# Compactly supported cohomology

Let `U` be separated of finite type over a Noetherian scheme `Y`, with a compactification
`j : U ⟶ X`, `X ⟶ Y` proper. [Stacks, Section 0G59] defines, for `K ∈ D^b_{Coh}(𝒪_U)` and a
Deligne system `(K_n)` for `j` with value `K`, `H^i_c(U, K) = lim_n H^i(X, K_n)`. Here it is
`Hom_{Pro}(𝒪_Y, Rg_!(K[i]))`, the morphisms from the constant pro-object at `𝒪_Y` into the image
of `K[i]` under the functor `Rg_! = Rp_* ∘ Rj_!` of [Stacks, Section 0G4Z]: for a Deligne system
`(K_n)` of `K[i]`, `Rg_!(K[i])` is the pro-object of `(Rp_* K_n)`, and morphisms from a constant
pro-object into it are the compatible families of morphisms `𝒪_Y ⟶ Rp_* K_n`, that is
`lim_n H^0(X, K_n)`.

This is the degree-`i` analogue of `AlgebraicGeometry.degreeZeroCompactSupport` of
[Stacks, Tag 0G5C] at an arbitrary compactification, and agrees with it, definitionally, at the
compactification of an open of a proper scheme by that scheme
(`AlgebraicGeometry.compactSupportCohomology_openCompactification`). Over a field `k` it is a
`k`-vector space, with the values computed pointwise
(`CategoryTheory.ProSeq.instModuleConstHom`), and a topological space, with the limit topology of
[Stacks, Section 0G59]: the coarsest topology making each projection to `Hom(𝒪_Y, Rp_* K_n)`
continuous for the discrete topology there.

## Main definitions

* `AlgebraicGeometry.compactSupportCohomology`: `H^i_c(U, K)`.
* `AlgebraicGeometry.compactSupportCohomologyMap`: its functoriality in `K`.
* `AlgebraicGeometry.compactSupportPresentationIso`: `Rg_! K = (Rp_* K_n)` for the assigned
  Deligne system `(K_n)` of [Stacks, Tag 0G4L].
* `AlgebraicGeometry.compactSupportProjection`: the projections `H^i_c(U, K) ⟶ H^i(X, K_n)`.
* `AlgebraicGeometry.compactSupportCohomologyLinearEquiv`:
  `H^i_c(U, K) = Hom_{Pro}(𝒪_X, Rj_!(K[i]))`, through `Hom_Y(𝒪_Y, Rp_* N) = Hom_X(𝒪_X, N)`.

## Implementation notes

The derived categories are at `CategoryTheory.HasDerivedCategory.standard`, the model of
`AlgebraicGeometry.BoundedCoherentDerived`, `CompactificationData.shriekImage`, the Deligne systems
of `AlgebraicGeometry.DeligneSystem.values` and
`AlgebraicGeometry.derivedGlobalSectionsOverPushforwardIso`; it is named in each statement that
needs it by `letI`, inlined at elaboration.

## References

* [Stacks Project, Section 0G59](https://stacks.math.columbia.edu/tag/0G59)
* [Stacks Project, Tag 0G5C](https://stacks.math.columbia.edu/tag/0G5C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

section General

variable {Y U : Scheme.{u}} [IsNoetherian Y] {p : U ⟶ Y} (c : CompactificationOf (Over.mk p))

/-- **Compactly supported cohomology** `H^i_c(U, K) = Hom_{Pro}(𝒪_Y, Rg_!(K[i]))` of
[Stacks, Section 0G59], for the compactification `c` of `p : U ⟶ Y`: for a Deligne system
`(K_n)` of `K[i]` along `c`, this is `lim_n Hom(𝒪_Y, Rp_* K_n) = lim_n H^i`. -/
public def compactSupportCohomology (L : BoundedCoherentDerived U) (i : ℤ) : Type (u + 1) :=
  ProSeq.const.obj (structureSheafBoundedCoherent Y) ⟶
    (CompactificationData.ofOpenImmersion c.immersion c.toBase).shriekImage.obj (L⟦i⟧)

/-- At the compactification of an open `V` of a proper `X` by `X`, compactly supported cohomology
in degree `i` is `AlgebraicGeometry.degreeZeroCompactSupport` of the shift by `i`. -/
public lemma compactSupportCohomology_openCompactification {X : Scheme.{u}} [IsNoetherian X]
    (q : X ⟶ Y) [IsProper q] (V : X.Opens) (L : BoundedCoherentDerived V) (i : ℤ) :
    compactSupportCohomology (openCompactification q V) L i =
      degreeZeroCompactSupport q V (L⟦i⟧) :=
  rfl

/-- The map `H^i_c(U, K) ⟶ H^i_c(U, K')` induced by `K ⟶ K'`. -/
public def compactSupportCohomologyMap {L L' : BoundedCoherentDerived U} (f : L ⟶ L') (i : ℤ) :
    compactSupportCohomology c L i → compactSupportCohomology c L' i :=
  fun y => y ≫ (CompactificationData.ofOpenImmersion c.immersion c.toBase).shriekImage.map (f⟦i⟧')

/-- `Rg_! K` is the pro-object of `(Rp_* K_n)`, for the Deligne system `(K_n)` assigned to `K`. -/
public def compactSupportPresentationIso (L : BoundedCoherentDerived U) :
    (CompactificationData.ofOpenImmersion c.immersion c.toBase).shriekImage.obj L ≅
      ProSeq.of ((DeligneSystem.values c.immersion).system L ⋙
        properPushforwardBoundedCoherent c.toBase) :=
  (ProSeq.map (properPushforwardBoundedCoherent c.toBase)).mapIso
      (extensionByZeroIso _ (DeligneSystem.values c.immersion).toAssignment L) ≪≫
    ProSeq.mapOfIso _ _

/-- The projection `H^i_c(U, K) ⟶ Hom(𝒪_Y, Rp_* K_n)` to the `n`-th term, for the Deligne system
`(K_n)` assigned to `K[i]`. -/
public def compactSupportProjection (L : BoundedCoherentDerived U) (i : ℤ) (n : ℕ)
    (y : compactSupportCohomology c L i) :
    structureSheafBoundedCoherent Y ⟶ (properPushforwardBoundedCoherent c.toBase).obj
      (((DeligneSystem.values c.immersion).system (L⟦i⟧)).obj (op n)) :=
  ProSeq.constHomComponent (y ≫ (compactSupportPresentationIso c (L⟦i⟧)).hom) n

/-- **The limit topology on `H^i_c(U, K)`** of [Stacks, Section 0G59]: the coarsest topology
making every projection to `Hom(𝒪_Y, Rp_* K_n)` continuous for the discrete topology. -/
public instance (L : BoundedCoherentDerived U) (i : ℤ) :
    TopologicalSpace (compactSupportCohomology c L i) :=
  ⨅ n : ℕ, TopologicalSpace.induced (compactSupportProjection c L i n) ⊥

end General

/-- `𝒪_X` in `D^b_{Coh}(𝒪_X)`, with underlying object `AlgebraicGeometry.derivedUnitObject X` of
`D(𝒪_X)`; it agrees definitionally with `AlgebraicGeometry.structureSheafBoundedCoherent X`. -/
public abbrev unitBoundedCoherent (X : Scheme.{u}) [IsLocallyNoetherian X] :
    BoundedCoherentDerived X :=
  letI := HasDerivedCategory.standard X.Modules
  ⟨derivedUnitObject X, (structureSheafBoundedCoherent X).property⟩

section Field

variable {k : Type u} [Field k] {U : Scheme.{u}} {p : U ⟶ Spec (CommRingCat.of k)}
  (c : CompactificationOf (Over.mk p))

/-- The canonical `k`-linear structure on `𝒪_{Spec k}`-modules,
`AlgebraicGeometry.modulesLinear`. -/
local instance linearModulesSpecField : Linear k (Spec (CommRingCat.of k)).Modules :=
  modulesLinear k (Over.mk (𝟙 _))

/-- The canonical `k`-linear structure on modules on a compactification over `k`. -/
local instance linearModulesCompactification : Linear k c.space.Modules :=
  modulesLinear k (Over.mk c.toBase)

/-- The additive group `H^i_c(U, K)`. -/
public instance (L : BoundedCoherentDerived U) (i : ℤ) :
    AddCommGroup (compactSupportCohomology c L i) :=
  inferInstanceAs (AddCommGroup (ProSeq.const.obj _ ⟶ _))

/-- **The `k`-vector space `H^i_c(U, K)`**, for the canonical `k`-linear structure on
`D^b_{Coh}(𝒪_{Spec k})`: the values of a morphism of pro-objects are added and scaled
pointwise. -/
public instance (L : BoundedCoherentDerived U) (i : ℤ) :
    Module k (compactSupportCohomology c L i) :=
  inferInstanceAs (Module k (ProSeq.const.obj _ ⟶ _))

/-- Morphisms of `D^b_{Coh}` are the morphisms of the underlying objects of `D(𝒪)`,
`k`-linearly. -/
public def boundedCoherentHomLinearEquiv {Z : Scheme.{u}} [Linear k Z.Modules]
    (A B : BoundedCoherentDerived Z) :
    letI := HasDerivedCategory.standard Z.Modules
    (A ⟶ B) ≃ₗ[k] (A.obj ⟶ B.obj) :=
  letI := HasDerivedCategory.standard Z.Modules
  {
  toFun f := f.hom
  invFun g := ObjectProperty.homMk g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl }

/-- The underlying morphism. -/
public lemma boundedCoherentHomLinearEquiv_apply {Z : Scheme.{u}} [Linear k Z.Modules]
    {A B : BoundedCoherentDerived Z} (f : A ⟶ B) :
    letI := HasDerivedCategory.standard Z.Modules
    boundedCoherentHomLinearEquiv (k := k) A B f = f.hom :=
  rfl

/-- The underlying morphism of the inverse. -/
public lemma boundedCoherentHomLinearEquiv_symm_apply_hom {Z : Scheme.{u}} [Linear k Z.Modules]
    {A B : BoundedCoherentDerived Z} (g : A.obj ⟶ B.obj) :
    letI := HasDerivedCategory.standard Z.Modules
    ((boundedCoherentHomLinearEquiv (k := k) A B).symm g).hom = g :=
  rfl

/-- **`Hom_{Spec k}(𝒪, Rq_* N) = Hom_X(𝒪_X, N)`** for `q : X ⟶ Spec k` the proper structure
morphism of the compactification and `N ∈ D^b_{Coh}(𝒪_X)`, in `D(𝒪)`, `k`-linearly: both sides
are `H^0(X, N)`, by `Hom(𝒪, -) = H^0` (`AlgebraicGeometry.structureSheafHomLinearEquiv`) on either
side and `RΓ(X, -) = RΓ(Spec k, Rq_* -)` ([Stacks, Tag 0D5W],
`AlgebraicGeometry.derivedGlobalSectionsOverPushforwardIso`). -/
public def structureSheafPushforwardDerivedHomLinearEquiv (N : BoundedCoherentDerived c.space) :
    letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
    letI := HasDerivedCategory.standard c.space.Modules
    ((structureSheafBoundedCoherent (Spec (CommRingCat.of k))).obj ⟶
        ((properPushforwardBoundedCoherent c.toBase).obj N).obj) ≃ₗ[k]
      (derivedUnitObject c.space ⟶ N.obj) :=
  letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
  letI := HasDerivedCategory.standard c.space.Modules
  letI := HasDerivedCategory.standard (ModuleCat.{u} k)
  (structureSheafHomLinearEquiv (𝟙 (Spec (CommRingCat.of k)))
      ((derivedPushforwardModules c.toBase).obj N.obj)).trans <|
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).mapIso
      ((derivedGlobalSectionsOverPushforwardIso c.toBase).app N.obj)).symm.toLinearEquiv.trans
    (structureSheafHomLinearEquiv c.toBase N.obj).symm

/-- `Hom(𝒪, Rq_* N) = Hom(𝒪_X, N)` is natural in `N`. -/
public lemma structureSheafPushforwardDerivedHomLinearEquiv_comp
    {N N' : BoundedCoherentDerived c.space} (g : N ⟶ N')
    (a : (structureSheafBoundedCoherent (Spec (CommRingCat.of k))).obj ⟶
      ((properPushforwardBoundedCoherent c.toBase).obj N).obj) :
    letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
    letI := HasDerivedCategory.standard c.space.Modules
    structureSheafPushforwardDerivedHomLinearEquiv c N'
        (a ≫ ((properPushforwardBoundedCoherent c.toBase).map g).hom) =
      structureSheafPushforwardDerivedHomLinearEquiv c N a ≫ g.hom := by
  let _ := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
  let _ := HasDerivedCategory.standard c.space.Modules
  let _ := HasDerivedCategory.standard (ModuleCat.{u} k)
  apply (structureSheafHomAddEquiv c.toBase N'.obj).injective
  show structureSheafHomAddEquiv c.toBase N'.obj
      ((structureSheafHomAddEquiv c.toBase N'.obj).symm _) =
    structureSheafHomAddEquiv c.toBase N'.obj
      ((structureSheafHomAddEquiv c.toBase N.obj).symm _ ≫ g.hom)
  rw [AddEquiv.apply_symm_apply, structureSheafHomAddEquiv_comp, AddEquiv.apply_symm_apply]
  have h₁ := structureSheafHomAddEquiv_comp (𝟙 (Spec (CommRingCat.of k))) a
    ((derivedPushforwardModules c.toBase).map g.hom)
  have h₂ := ConcreteCategory.congr_hom
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).congr_map
      ((derivedGlobalSectionsOverPushforwardIso c.toBase).inv.naturality g.hom))
    (structureSheafHomAddEquiv (𝟙 (Spec (CommRingCat.of k)))
      ((derivedPushforwardModules c.toBase).obj N.obj) a)
  simp only [Functor.map_comp, ConcreteCategory.comp_apply] at h₂
  refine (congrArg (fun z => ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
    ((derivedGlobalSectionsOverPushforwardIso c.toBase).inv.app N'.obj)).hom z) h₁).trans ?_
  exact h₂

/-- **`Hom_{Spec k}(𝒪, Rq_* N) = Hom_X(𝒪_X, N)`** on `D^b_{Coh}`. -/
public def structureSheafPushforwardHomLinearEquiv (N : BoundedCoherentDerived c.space) :
    (structureSheafBoundedCoherent (Spec (CommRingCat.of k)) ⟶
        (properPushforwardBoundedCoherent c.toBase).obj N) ≃ₗ[k]
      (unitBoundedCoherent c.space ⟶ N) :=
  letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
  letI := HasDerivedCategory.standard c.space.Modules
  letI := HasDerivedCategory.standard (ModuleCat.{u} k)
  (boundedCoherentHomLinearEquiv _ _).trans
    ((structureSheafPushforwardDerivedHomLinearEquiv c N).trans
      (boundedCoherentHomLinearEquiv (unitBoundedCoherent c.space) N).symm)

/-- The value of `AlgebraicGeometry.structureSheafPushforwardHomLinearEquiv`. -/
public lemma structureSheafPushforwardHomLinearEquiv_apply_hom (N : BoundedCoherentDerived c.space)
    (a : structureSheafBoundedCoherent (Spec (CommRingCat.of k)) ⟶
      (properPushforwardBoundedCoherent c.toBase).obj N) :
    letI := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
    letI := HasDerivedCategory.standard c.space.Modules
    (structureSheafPushforwardHomLinearEquiv c N a).hom =
      (structureSheafPushforwardDerivedHomLinearEquiv c N) a.hom := by
  let _ := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
  let _ := HasDerivedCategory.standard c.space.Modules
  let _ := HasDerivedCategory.standard (ModuleCat.{u} k)
  rw [structureSheafPushforwardHomLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    boundedCoherentHomLinearEquiv_symm_apply_hom, boundedCoherentHomLinearEquiv_apply]

/-- `Hom(𝒪, Rq_* N) = Hom(𝒪_X, N)` is natural in `N`. -/
public lemma structureSheafPushforwardHomLinearEquiv_comp {N N' : BoundedCoherentDerived c.space}
    (g : N ⟶ N') (a : structureSheafBoundedCoherent (Spec (CommRingCat.of k)) ⟶
      (properPushforwardBoundedCoherent c.toBase).obj N) :
    structureSheafPushforwardHomLinearEquiv c N'
        (a ≫ (properPushforwardBoundedCoherent c.toBase).map g) =
      structureSheafPushforwardHomLinearEquiv c N a ≫ g := by
  let _ := HasDerivedCategory.standard (Spec (CommRingCat.of k)).Modules
  let _ := HasDerivedCategory.standard c.space.Modules
  let _ := HasDerivedCategory.standard (ModuleCat.{u} k)
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    structureSheafPushforwardHomLinearEquiv_apply_hom]
  exact structureSheafPushforwardDerivedHomLinearEquiv_comp c g a.hom

/-- **`H^i_c(U, K) = Hom_{Pro}(𝒪_X, Rj_!(K[i]))`**, `k`-linearly: morphisms from `𝒪_{Spec k}` into
`Rg_!(K[i]) = Rq_* Rj_!(K[i])` are morphisms from `𝒪_X` into `Rj_!(K[i])`, through
`Hom(𝒪_{Spec k}, Rq_* -) = Hom(𝒪_X, -)` (`CategoryTheory.ProSeq.homConstMapLinearEquiv`). -/
public abbrev compactSupportCohomologyLinearEquiv (L : BoundedCoherentDerived U) (i : ℤ) :
    compactSupportCohomology c L i ≃ₗ[k]
      (ProSeq.const.obj (unitBoundedCoherent c.space) ⟶
        (extensionByZeroOpenImmersion c.immersion).obj (L⟦i⟧)) :=
  ProSeq.homConstMapLinearEquiv (properPushforwardBoundedCoherent c.toBase)
    (structureSheafPushforwardHomLinearEquiv c)
    (structureSheafPushforwardHomLinearEquiv_comp c) _


end Field

end AlgebraicGeometry

end
