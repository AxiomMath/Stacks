module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Category.Preorder
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.GlobalSectionsTensor

/-!
# The module `𝒪_X ⊗_R M` over a base ring, and the comparison map of an inverse limit

Let `(C, J)` be a site, let `O` be a sheaf of commutative rings on it and write `A = Γ(C, O)` for
the ring of global functions.  A morphism `f : X → Spec(R)` is the same datum as a ring map
`R → Γ(X, 𝒪_X)`, so a base ring for `O` is a commutative ring `R` together with a ring map
`φ : R →+* A`.  For an `R`-module `M` the module `𝒪_X ⊗_R M` of Stacks 0D3F is then
`𝒪_X ⊗_A (A ⊗_R M)`, that is, the sheafification of `U ↦ 𝒪_X(U) ⊗_R M`: it is the composite of
extension of scalars along `φ` with the functor `M ↦ M ⊗_A 𝒪` of
`Stacks.Cohomology.SiteModules.sectionTensorSheafFunctor`.

Being a composite of two left adjoints it is left adjoint to global sections read as `R`-modules,
which is the mapping property of Tag 01BH: morphisms `𝒪_X ⊗_R M ⟶ F` are the `R`-linear maps
`M ⟶ Γ(X, F)`, by composition with a unit natural in `M`.  An adjunction determines its left
adjoint up to unique natural isomorphism, so this pins the module `𝒪_X ⊗_R M` rather than merely
exhibiting one construction of it.

For an inverse system `(M_n)` of `R`-modules the functor carries a limit cone of `(M_n)` to a cone
over the system `(𝒪_X ⊗_R M_n)`, and the induced map out of the image of the limit into a limit of
that system is the canonical map
`𝒪_X ⊗_R (lim M_n) ⟶ lim (𝒪_X ⊗_R M_n)`
of Stacks 0D3F.

## Main definitions

* `Stacks.Cohomology.SiteModules.baseRingTensorFunctor`: the functor `M ↦ 𝒪_X ⊗_R M` from
  `R`-modules to `O`-modules attached to a base ring `R` of `O`.
* `Stacks.Cohomology.SiteModules.baseRingGlobalSectionsFunctor`: global sections of an `O`-module,
  read as an `R`-module through `φ`.
* `Stacks.Cohomology.SiteModules.baseRingTensorUnit`: the canonical `R`-linear map
  `M ⟶ Γ(X, 𝒪_X ⊗_R M)`.
* `Stacks.Cohomology.SiteModules.baseRingTensorLimitComparison`: the canonical map
  `𝒪_X ⊗_R (lim M_n) ⟶ lim (𝒪_X ⊗_R M_n)`.

## Main results

* `Stacks.Cohomology.SiteModules.baseRingTensorAdjunction`: `M ↦ 𝒪_X ⊗_R M` is left adjoint to
  global sections read as `R`-modules, with
  `Stacks.Cohomology.SiteModules.baseRingTensorHomEquiv` the resulting bijection and
  `Stacks.Cohomology.SiteModules.baseRingTensorHomEquiv_apply` the statement that it is
  composition with the unit on global sections.
* `Stacks.Cohomology.SiteModules.baseRingTensorUnit_naturality`: the unit is natural in the
  module.
* `Stacks.Cohomology.SiteModules.baseRingTensorLimitComparison_fac` and
  `Stacks.Cohomology.SiteModules.baseRingTensorLimitComparison_uniq`: the comparison map is the
  unique map compatible with the two cones.
* `Stacks.Cohomology.SiteModules.bijective_comp_baseRingTensorLimitComparison_iff`: for a module
  of the form `𝒪_X ⊗_R N`, the comparison map induces a bijection on morphisms out of it exactly
  when the induced map on global sections induces a bijection on `R`-linear maps out of `N`.

## What this file does not prove

Tag 0D3F asserts more than the above: when `f : X → Spec(R)` is proper, flat and of finite
presentation and the transition maps of `(M_n)` are surjective, the comparison map above induces
an isomorphism from its source onto `DQ_X` applied to its target — equivalently, composition with
it is bijective on morphisms out of *every* object of `D_QCoh(𝒪_X)`, not only out of the modules
`𝒪_X ⊗_R N` treated here.  That assertion is **not** proved here, and no declaration in this file
assumes it.  Its proof in the source reduces to perfect `E` using a perfect generator of
`D_QCoh(𝒪_X)` (Tag 09IY), replaces the ordinary limit by the derived limit (Tag 0D3E, clause (1)),
exchanges `R Hom_X(E, -)` with the derived limit, identifies each term with
`R Γ(X, E^∨) ⊗^L_R M_n` by the projection formula (Tag 08IN) and the perfectness of `R Γ(X, E^∨)`
(Tag 0CTM), and concludes with Tag 0D2L.  Of these the repository carries Tag 0D2L
(`Stacks.PseudoCoherent.DerivedInverseLimit.derivedLimit_tensor_iso`) and all three clauses of
Tag 0D3E — clause (1) being
`AlgebraicGeometry.Space.isLimit_homology_of_isDerivedLimit`.  It
carries
no form of 09IY, 08IN or 0CTM, and there is no statement exchanging `R Hom_X(E, -)` with a derived
limit in the covariant variable; that last one belongs to no tag — Tag 0A0A is the
*contravariant* statement, carried once as
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit`.

## Implementation notes

The base ring is presented as a ring map `φ : R →+* Γ(C, O)` rather than as a morphism of algebraic
spaces, so the file applies to any site; the small étale site of an algebraic space `X` with a
morphism to `Spec(R)` is an instance, its structure sheaf being
`AlgebraicGeometry.Space.structureRingSheaf`.  The datum is the same one that
`Stacks.Cohomology.SiteModules.AlgebraSheaf.toGlobalSections` produces from a sheaf of
`R`-algebra structures on `O`.  No properness, flatness or finite-presentation hypothesis appears,
because nothing proved here uses one.

The module universe is `max u r w` with `w` free, as for
`Stacks.Cohomology.SiteModules.sectionTensorSheafFunctor`: it must contain the universe `u` of the
objects of the site, which global sections raise it to, and the universe `r` of the rings of
sections of `O`, which extension of scalars raises it to.  The universe of `R` itself is
independent of both, since extension of scalars along a ring map allows the two rings to lie in
unrelated universes.

Quasi-coherence of the values is not stated here.  `𝒪_X ⊗_R M` is
`sectionTensorSheafFunctor O` applied to `A ⊗_R M`, so
`Stacks.Cohomology.SiteModules.isQuasicoherentOnSite_sectionTensor` gives it wherever that lemma
applies; that lemma is pinned to module universe equal to the universe of the ring sheaf, because
`SheafOfModules.free` and `SheafOfModules.Presentation` are, and on the small étale site of an
algebraic space the objects of the site lie one universe above the rings of sections, so the two
universes differ there.

Limit cones are taken as data together with the witnesses that they are limits, so nothing here
depends on the availability of a chosen limit.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 07UZ](https://stacks.math.columbia.edu/tag/07UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r w t

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {O : Sheaf J CommRingCat.{r}}
  [HasWeakSheafify J AddCommGrpCat.{max u r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r w}]
  {R : Type t} [CommRing R]

/-- **The module `𝒪_X ⊗_R M` of Stacks 0D3F.** For a base ring `R` of `O`, given by a ring map
`φ : R →+* Γ(C, O)`, this is the sheafification of `U ↦ 𝒪_X(U) ⊗_R M`, obtained as the module
`(A ⊗_R M) ⊗_A 𝒪` attached to the `A`-module `A ⊗_R M`. -/
def baseRingTensorFunctor (φ : R →+* GlobalFunctionRing O) :
    ModuleCat.{max u r w} R ⥤ SheafOfModules.{max u r w} (ringSheafOfSite O) :=
  ModuleCat.extendScalars φ ⋙ sectionTensorSheafFunctor.{u, v, r, w} O

/-- Global sections of an `O`-module, read as a module over the base ring `R` through `φ`. -/
def baseRingGlobalSectionsFunctor (φ : R →+* GlobalFunctionRing O) :
    SheafOfModules.{max u r w} (ringSheafOfSite O) ⥤ ModuleCat.{max u r w} R :=
  globalSectionsFunctor (ringSheafOfSite O) ⋙ ModuleCat.restrictScalars φ

/-- **The mapping property of `𝒪_X ⊗_R M`**, Tag 01BH for a base ring: morphisms of `O`-modules
`𝒪_X ⊗_R M ⟶ F` are the `R`-linear maps `M ⟶ Γ(X, F)`.

It is the composite of the adjunction between extension and restriction of scalars along `φ` with
`Stacks.Cohomology.SiteModules.sectionTensorSheafAdjunction`.  Since an adjunction determines its
left adjoint up to unique natural isomorphism, this characterises `𝒪_X ⊗_R M`. -/
def baseRingTensorAdjunction (φ : R →+* GlobalFunctionRing O) :
    baseRingTensorFunctor φ ⊣ baseRingGlobalSectionsFunctor φ :=
  (ModuleCat.extendRestrictScalarsAdj.{w, t, max u r} φ).comp
    (sectionTensorSheafAdjunction.{u, v, r, w} O)

variable (φ : R →+* GlobalFunctionRing O)

/-- Morphisms of `O`-modules out of `𝒪_X ⊗_R M` are the `R`-linear maps from `M` to global
sections. -/
def baseRingTensorHomEquiv (M : ModuleCat.{max u r w} R)
    (F : SheafOfModules.{max u r w} (ringSheafOfSite O)) :
    ((baseRingTensorFunctor φ).obj M ⟶ F) ≃ (M ⟶ (baseRingGlobalSectionsFunctor φ).obj F) :=
  (baseRingTensorAdjunction φ).homEquiv M F

/-- The canonical `R`-linear map from `M` to the global sections of `𝒪_X ⊗_R M`. -/
def baseRingTensorUnit (M : ModuleCat.{max u r w} R) :
    M ⟶ (baseRingGlobalSectionsFunctor φ).obj ((baseRingTensorFunctor φ).obj M) :=
  (baseRingTensorAdjunction φ).unit.app M

/-- The mapping property is given by composition with the unit on global sections. -/
theorem baseRingTensorHomEquiv_apply (M : ModuleCat.{max u r w} R)
    (F : SheafOfModules.{max u r w} (ringSheafOfSite O))
    (a : (baseRingTensorFunctor φ).obj M ⟶ F) :
    baseRingTensorHomEquiv φ M F a =
      baseRingTensorUnit φ M ≫ (baseRingGlobalSectionsFunctor φ).map a :=
  (baseRingTensorAdjunction φ).homEquiv_unit M F a

/-- The canonical map to the global sections of `𝒪_X ⊗_R M` is natural in `M`. -/
theorem baseRingTensorUnit_naturality {M N : ModuleCat.{max u r w} R} (g : M ⟶ N) :
    g ≫ baseRingTensorUnit φ N =
      baseRingTensorUnit φ M ≫
        (baseRingGlobalSectionsFunctor φ).map ((baseRingTensorFunctor φ).map g) :=
  (baseRingTensorAdjunction φ).unit.naturality g

/-- **Composition with a morphism of `O`-modules is bijective on morphisms out of `𝒪_X ⊗_R N`
exactly when composition with the induced map on global sections is bijective on the `R`-linear
maps out of `N`.**  Both maps are conjugate by the bijections of the mapping property, which is
natural in the target. -/
theorem bijective_comp_iff_bijective_comp_globalSections (N : ModuleCat.{max u r w} R)
    {F₁ F₂ : SheafOfModules.{max u r w} (ringSheafOfSite O)} (ψ : F₁ ⟶ F₂) :
    Function.Bijective (fun a : (baseRingTensorFunctor φ).obj N ⟶ F₁ => a ≫ ψ) ↔
      Function.Bijective (fun b : N ⟶ (baseRingGlobalSectionsFunctor φ).obj F₁ =>
        b ≫ (baseRingGlobalSectionsFunctor φ).map ψ) := by
  have key : (fun b : N ⟶ (baseRingGlobalSectionsFunctor φ).obj F₁ =>
        b ≫ (baseRingGlobalSectionsFunctor φ).map ψ) ∘ ⇑(baseRingTensorHomEquiv φ N F₁) =
      ⇑(baseRingTensorHomEquiv φ N F₂) ∘
        (fun a : (baseRingTensorFunctor φ).obj N ⟶ F₁ => a ≫ ψ) := by
    funext a
    exact ((baseRingTensorAdjunction φ).homEquiv_naturality_right a ψ).symm
  calc Function.Bijective (fun a : (baseRingTensorFunctor φ).obj N ⟶ F₁ => a ≫ ψ)
      ↔ Function.Bijective (⇑(baseRingTensorHomEquiv φ N F₂) ∘
            (fun a : (baseRingTensorFunctor φ).obj N ⟶ F₁ => a ≫ ψ)) :=
        ((baseRingTensorHomEquiv φ N F₂).bijective.of_comp_iff' _).symm
    _ ↔ Function.Bijective ((fun b : N ⟶ (baseRingGlobalSectionsFunctor φ).obj F₁ =>
            b ≫ (baseRingGlobalSectionsFunctor φ).map ψ) ∘
          ⇑(baseRingTensorHomEquiv φ N F₁)) := by rw [key]
    _ ↔ Function.Bijective (fun b : N ⟶ (baseRingGlobalSectionsFunctor φ).obj F₁ =>
            b ≫ (baseRingGlobalSectionsFunctor φ).map ψ) :=
        (baseRingTensorHomEquiv φ N F₁).bijective.of_comp_iff _

section InverseLimit

variable (Msys : ℕᵒᵖ ⥤ ModuleCat.{max u r w} R) (c : Cone Msys)
  (d : Cone (Msys ⋙ baseRingTensorFunctor φ)) (hd : IsLimit d)

/-- **The canonical map `𝒪_X ⊗_R (lim M_n) ⟶ lim (𝒪_X ⊗_R M_n)` of Stacks 0D3F**: the map out of
the image of a limit cone of the inverse system induced by a limit cone of its image. -/
def baseRingTensorLimitComparison : (baseRingTensorFunctor φ).obj c.pt ⟶ d.pt :=
  hd.lift ((baseRingTensorFunctor φ).mapCone c)

/-- The comparison map is compatible with the two cones: followed by the `n`-th projection of the
limit of `(𝒪_X ⊗_R M_n)` it is the image of the `n`-th projection of the limit of `(M_n)`. -/
theorem baseRingTensorLimitComparison_fac (n : ℕᵒᵖ) :
    baseRingTensorLimitComparison φ Msys c d hd ≫ d.π.app n =
      (baseRingTensorFunctor φ).map (c.π.app n) :=
  hd.fac ((baseRingTensorFunctor φ).mapCone c) n

/-- The comparison map is the only map compatible with the two cones. -/
theorem baseRingTensorLimitComparison_uniq
    (m : (baseRingTensorFunctor φ).obj c.pt ⟶ d.pt)
    (hm : ∀ n : ℕᵒᵖ, m ≫ d.π.app n = (baseRingTensorFunctor φ).map (c.π.app n)) :
    m = baseRingTensorLimitComparison φ Msys c d hd :=
  hd.uniq ((baseRingTensorFunctor φ).mapCone c) m hm

/-- Composing with the comparison map and passing to the mapping property is passing to the
mapping property and composing with the induced map on global sections. -/
theorem homEquiv_comp_baseRingTensorLimitComparison (N : ModuleCat.{max u r w} R)
    (a : (baseRingTensorFunctor φ).obj N ⟶ (baseRingTensorFunctor φ).obj c.pt) :
    baseRingTensorHomEquiv φ N d.pt (a ≫ baseRingTensorLimitComparison φ Msys c d hd) =
      baseRingTensorHomEquiv φ N ((baseRingTensorFunctor φ).obj c.pt) a ≫
        (baseRingGlobalSectionsFunctor φ).map (baseRingTensorLimitComparison φ Msys c d hd) :=
  (baseRingTensorAdjunction φ).homEquiv_naturality_right a
    (baseRingTensorLimitComparison φ Msys c d hd)

/-- **The comparison map is bijective on morphisms out of `𝒪_X ⊗_R N` exactly when the induced
map on global sections is bijective on `R`-linear maps out of `N`.**  This is the reduction of the
Hom-formulation of Stacks 0D3F for the modules `𝒪_X ⊗_R N`; it holds with no hypothesis on the
inverse system or on the site, because it is the mapping property applied twice. -/
theorem bijective_comp_baseRingTensorLimitComparison_iff (N : ModuleCat.{max u r w} R) :
    Function.Bijective
        (fun a : (baseRingTensorFunctor φ).obj N ⟶ (baseRingTensorFunctor φ).obj c.pt =>
          a ≫ baseRingTensorLimitComparison φ Msys c d hd) ↔
      Function.Bijective
        (fun b : N ⟶ (baseRingGlobalSectionsFunctor φ).obj ((baseRingTensorFunctor φ).obj c.pt) =>
          b ≫ (baseRingGlobalSectionsFunctor φ).map
            (baseRingTensorLimitComparison φ Msys c d hd)) :=
  bijective_comp_iff_bijective_comp_globalSections φ N
    (baseRingTensorLimitComparison φ Msys c d hd)

end InverseLimit

end Stacks.Cohomology.SiteModules

end
