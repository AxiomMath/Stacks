module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.PolynomialChart
public import StacksFrontier.Cotangent.StandardResolution
public import StacksFrontier.Cotangent.StandardResolutionIsResolution

/-!
# The standard resolutions of the sections of a scheme as cosimplicial polynomial charts

Let `Λ` be a ring, let `X` be a scheme over `Λ` and let `C_{X/Λ}` be its category of polynomial
charts: the commutative diagrams `U ⟶ A ⟶ Spec Λ`, `U ⟶ X ⟶ Spec Λ` with `U` an open subscheme
of `X` and `A` an affine space over `Spec Λ`. For an open `U ⊆ X` let `P_{•,U}` be the standard
resolution of `𝒪_X(U)` over `Λ` and put `A_{n,U} = Spec(P_{n,U})`. Then `A_{•,U}` is a
cosimplicial object of the fibre category of `C_{X/Λ}` over `U`, and the construction is
functorial in `U`: a smaller open `U' ⊆ U` restricts the sections, hence maps the standard
resolution `P_{•,U} ⟶ P_{•,U'}`, hence maps the affine spaces `A_{•,U'} ⟶ A_{•,U}` over `U' ⊆ U`.
Consequently, for every presheaf `ℱ` on `C_{X/Λ}` with values in a preadditive category, the
degreewise evaluations `U ↦ ℱ(A_{n,U})` assemble into a complex of presheaves `U ↦ ℱ(A_{•,U})`
on the small Zariski site of `X`.

## Main definitions

* `AlgebraicGeometry.PolynomialChart.openAlgebra`: the functor `U ↦ 𝒪_X(U)` from the opens of `X`
  to commutative `Λ`-algebras, the `Λ`-algebra structure coming from the structure morphism.
* `AlgebraicGeometry.PolynomialChart.ofAugmentation` and
  `AlgebraicGeometry.PolynomialChart.homOfAugmentation`: the polynomial chart attached to a
  presented polynomial `Λ`-algebra with an augmentation to `𝒪_X(U)`, and the chart morphism
  attached to a morphism of such data over an inclusion of opens.
* `AlgebraicGeometry.PolynomialChart.openStandardResolution`: the standard resolution of `𝒪_X(U)`
  over `Λ`, functorially in `U`.
* `AlgebraicGeometry.PolynomialChart.standardResolutionChart`: the functorial cosimplicial
  polynomial charts `U ↦ A_{•,U}`.
* `AlgebraicGeometry.PolynomialChart.standardResolutionFibreChart`: the same, read as a
  cosimplicial object of the fibre category of `C_{X/Λ}` over `U`.
* `AlgebraicGeometry.PolynomialChart.standardResolutionEvaluation` and
  `AlgebraicGeometry.PolynomialChart.standardResolutionComplex`: the simplicial presheaf
  `U ↦ ℱ(A_{•,U})` obtained by evaluating a presheaf on the cosimplicial charts, and its
  alternating face map complex.

## Main results

* `AlgebraicGeometry.PolynomialChart.openRingIsoSections`: the ring of functions used here is the
  ring of sections of `𝒪_X` over `U`.
* `AlgebraicGeometry.PolynomialChart.openToSpec_comm` and
  `AlgebraicGeometry.PolynomialChart.openToSpec_naturality`: the canonical morphism from an open
  subscheme to the spectrum of its own ring of functions lies over `Spec Λ` and is natural in the
  open. These two facts are what make the charts below commute.
* `AlgebraicGeometry.PolynomialChart.standardResolutionChart_comp_openFunctor`: `A_{•,U}` lies in
  the fibre over `U`, which is what `standardResolutionFibreChart` records.
* `AlgebraicGeometry.PolynomialChart.isResolution_openStandardResolution`: for every open `U` the
  standard resolution of `𝒪_X(U)` over `Λ` is a resolution in the sense of Tag 08QI.
* `AlgebraicGeometry.PolynomialChart.standardResolutionEvaluation_comp_evaluation`: the value at
  `U` of the simplicial presheaf is the simplicial object `ℱ(A_{•,U})`, on the nose.

## Implementation notes

The ring of functions on an open `U` is taken to be `Γ(U, ⊤)`, the global sections of the open
subscheme `U` regarded as a scheme, rather than `Γ(X, U)`; the two agree by
`AlgebraicGeometry.Scheme.Opens.topIso`, and the former is the one for which the comparison
morphism `U ⟶ Spec 𝒪_X(U)` is literally `AlgebraicGeometry.Scheme.toSpecΓ`, so that the two
geometric facts above are the naturality of `toSpecΓ` and nothing more. The `Λ`-algebra structure
is produced through `commAlgCatEquivUnder`, which identifies commutative `Λ`-algebras with
commutative rings under `Λ`: a functor to rings under `Λ` is immediate from the structure
morphism, whereas a functor to `CommAlgCat Λ` written out by hand carries a different `Algebra`
instance at every open.

A chart records its affine space together with an isomorphism to the spectrum of an explicit
polynomial ring, and that isomorphism is unconstrained by the morphisms of charts. So
`ofAugmentation` takes the presentation as a separate argument and uses the spectrum of the given
algebra itself as the affine space; the presentation of a term of the standard resolution is then
`CommAlgCat.standardResolution_obj_mvPolynomial`, whose index type is the iterate of the
polynomial-algebra comonad.

`isResolution_openStandardResolution` pins the `CommRing` and `Algebra` instances of its algebra
to the structure fields of `CommAlgCat`. Left to instance search the ring structure is found
through the forgetful functor of the concrete category instead, and the `Algebra` instance, which
is a field of the same structure, then no longer matches it.

The computation of Tag 08VB itself — that `A_{•,U}` is a point resolution of the fibre in the
sense of Tag 08Q9, that the cohomology of the complex of presheaves computes the homology of the
fibre, and that its sheafification computes `Lπ_!` — is
`StacksFrontier/Cotangent/StandardResolutionChartsLowerShriek.lean`, from the computation of derived
lower shriek by fibrewise point resolutions of an arbitrary fibred category in
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/PointResolution/`.

## References

* [Stacks Project, Tag 08VB](https://stacks.math.columbia.edu/tag/08VB)
* [Stacks Project, Tag 08V7](https://stacks.math.columbia.edu/tag/08V7)
* [Stacks Project, Tag 08PM](https://stacks.math.columbia.edu/tag/08PM)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicTopology Opposite Simplicial

universe u v w

noncomputable section

namespace AlgebraicGeometry.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
  (structureMap : X ⟶ Spec (CommRingCat.of Λ))

/-! ### The functions on an open subscheme as a `Λ`-algebra -/

/-- The ring map `Λ ⟶ Γ(X, 𝒪_X)` given by the structure morphism `X ⟶ Spec Λ`. -/
def baseRingHom : CommRingCat.of Λ ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ structureMap.appTop

/-- The structure morphism of `X` over `Λ` is the one induced by `Λ ⟶ Γ(X, 𝒪_X)`. -/
theorem structureMap_eq : structureMap = X.toSpecΓ ≫ Spec.map (baseRingHom Λ X structureMap) := by
  rw [baseRingHom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The functor sending an open subscheme `U` of `X` to the ring `𝒪_X(U)` under `Λ`. -/
def openUnder : X.Opensᵒᵖ ⥤ Under (CommRingCat.of Λ) where
  obj U := Under.mk (baseRingHom Λ X structureMap ≫ (U.unop.ι).appTop)
  map {U V} f := Under.homMk ((X.homOfLE (leOfHom f.unop)).appTop) (by
    simp only [Under.mk_right, Under.mk_hom, Category.assoc]
    rw [← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι])
  map_id U := by ext; simp
  map_comp f g := by
    ext
    simp only [Under.comp_right, Under.homMk_right]
    rw [← Scheme.Hom.comp_appTop, Scheme.homOfLE_homOfLE]

/-- The functor sending an open subscheme `U` of `X` to the `Λ`-algebra `𝒪_X(U)`. -/
def openAlgebra : X.Opensᵒᵖ ⥤ CommAlgCat.{u} Λ :=
  openUnder Λ X structureMap ⋙ (commAlgCatEquivUnder (CommRingCat.of Λ)).inverse

/-- The underlying ring of `openAlgebra`. -/
abbrev openRing : X.Opensᵒᵖ ⥤ CommRingCat.{u} :=
  openAlgebra Λ X structureMap ⋙ forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}

/-- The value of `openRing` at `U` is the ring of global sections of the open subscheme `U`. -/
theorem openRing_obj (U : X.Opens) :
    (openRing Λ X structureMap).obj (op U) = Γ((U : Scheme.{u}), ⊤) := rfl

/-- The restriction maps of `openRing` are restriction of functions along the inclusions of open
subschemes. -/
theorem openRing_map {U V : X.Opens} (h : U ≤ V) :
    (openRing Λ X structureMap).map (homOfLE h).op = (X.homOfLE h).appTop := rfl

/-- The structure map of the `Λ`-algebra of functions on `U` is `Λ ⟶ Γ(X, 𝒪_X) ⟶ 𝒪_X(U)`. -/
theorem algebraMap_openAlgebra (U : X.Opens) :
    CommRingCat.ofHom (algebraMap Λ ((openAlgebra Λ X structureMap).obj (op U)))
      = baseRingHom Λ X structureMap ≫ U.ι.appTop := rfl

/-- The ring of functions used here is the ring of sections of `𝒪_X` over `U`. -/
def openRingIsoSections (U : X.Opens) :
    (openRing Λ X structureMap).obj (op U) ≅ Γ(X, U) :=
  U.topIso

/-- The canonical morphism from an open subscheme to the spectrum of its ring of functions. -/
def openToSpec (U : X.Opens) :
    (U : Scheme.{u}) ⟶ Spec ((openRing Λ X structureMap).obj (op U)) :=
  (U : Scheme.{u}).toSpecΓ

/-- `openToSpec` is a morphism over `Spec Λ`. -/
theorem openToSpec_comm (U : X.Opens) :
    openToSpec Λ X structureMap U ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap Λ ((openAlgebra Λ X structureMap).obj (op U))))
      = U.ι ≫ structureMap := by
  change (U : Scheme.{u}).toSpecΓ ≫ Spec.map (baseRingHom Λ X structureMap ≫ U.ι.appTop)
      = U.ι ≫ structureMap
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← structureMap_eq]

/-- `openToSpec` is natural in the open subscheme. -/
theorem openToSpec_naturality {U V : X.Opens} (h : U ≤ V) :
    X.homOfLE h ≫ openToSpec Λ X structureMap V
      = openToSpec Λ X structureMap U ≫
        Spec.map ((openRing Λ X structureMap).map (homOfLE h).op) := by
  change X.homOfLE h ≫ (V : Scheme.{u}).toSpecΓ
      = (U : Scheme.{u}).toSpecΓ ≫ Spec.map ((X.homOfLE h).appTop)
  rw [Scheme.toSpecΓ_naturality]

/-! ### Polynomial charts from augmented polynomial algebras -/

/-- A morphism of `Λ`-algebras commutes with the structure maps from `Λ`. -/
@[simp]
theorem algebraMap_comp {P Q : CommAlgCat.{u} Λ} (ψ : P ⟶ Q) :
    CommRingCat.ofHom (algebraMap Λ P) ≫
        (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map ψ
      = CommRingCat.ofHom (algebraMap Λ Q) := by
  rw [CommAlgCat.forget₂_commRingCat_map, ← CommRingCat.ofHom_comp]
  congr 1
  exact ψ.hom.comp_algebraMap

/-- The same for a polynomial algebra, whose structure map is the inclusion of constants. -/
theorem ofHom_C_comp {ι : Type u} {Q : CommAlgCat.{u} Λ}
    (ψ : CommAlgCat.of Λ (MvPolynomial ι Λ) ⟶ Q) :
    CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial ι Λ) ≫
        (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map ψ
      = CommRingCat.ofHom (algebraMap Λ Q) := by
  rw [← MvPolynomial.algebraMap_eq]
  exact algebraMap_comp Λ ψ

variable {Λ X structureMap}

/-- Two morphisms of polynomial charts agree as soon as their maps of affine spaces do: the
inclusion of open subschemes they lie over is a proposition. -/
@[ext]
theorem hom_ext {P Q : PolynomialChart Λ X structureMap} {f g : P ⟶ Q}
    (h : f.affine = g.affine) : f = g :=
  Hom.ext h

/-- The identity morphism of a polynomial chart is the identity on the affine space. -/
@[simp]
theorem id_affine (P : PolynomialChart Λ X structureMap) : (𝟙 P : P ⟶ P).affine = 𝟙 _ := rfl

/-- Composing morphisms of polynomial charts composes their maps of affine spaces. -/
@[simp]
theorem comp_affine {P Q R : PolynomialChart Λ X structureMap} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).affine = f.affine ≫ g.affine := rfl

/-- The polynomial chart attached to a polynomial `Λ`-algebra `P` presented on `ι` together with
an augmentation `P ⟶ 𝒪_X(U)`. -/
@[implicit_reducible]
def ofAugmentation {U : X.Opens} {ι : Type u} {P : CommAlgCat.{u} Λ}
    (e : P ≅ CommAlgCat.of Λ (MvPolynomial ι Λ))
    (φ : P ⟶ (openAlgebra Λ X structureMap).obj (op U)) :
    PolynomialChart Λ X structureMap where
  openPart := U
  variableIndex := ι
  affineSpace := Spec ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).obj P)
  affineEquiv :=
    Scheme.Spec.mapIso (((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).mapIso e).symm.op)
  toAffine := openToSpec Λ X structureMap U ≫
    Spec.map ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map φ)
  comm := by
    change (openToSpec Λ X structureMap U ≫
          Spec.map ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map φ)) ≫
        Spec.map ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map e.inv) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial ι Λ))
      = U.ι ≫ structureMap
    rw [← openToSpec_comm Λ X structureMap U]
    simp only [← Spec.map_comp, Category.assoc, ofHom_C_comp, algebraMap_comp]

/-- The open subscheme of `ofAugmentation e φ` is the one its augmentation is taken over. -/
@[simp]
theorem ofAugmentation_openPart {U : X.Opens} {ι : Type u} {P : CommAlgCat.{u} Λ}
    (e : P ≅ CommAlgCat.of Λ (MvPolynomial ι Λ))
    (φ : P ⟶ (openAlgebra Λ X structureMap).obj (op U)) :
    (ofAugmentation e φ).openPart = U := rfl

/-- The affine space of `ofAugmentation e φ` is the spectrum of the given algebra. -/
theorem ofAugmentation_affineSpace {U : X.Opens} {ι : Type u} {P : CommAlgCat.{u} Λ}
    (e : P ≅ CommAlgCat.of Λ (MvPolynomial ι Λ))
    (φ : P ⟶ (openAlgebra Λ X structureMap).obj (op U)) :
    (ofAugmentation e φ).affineSpace
      = Spec ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).obj P) := rfl

/-- The arrow from the open subscheme to the affine space of `ofAugmentation e φ` is the one the
augmentation induces through the `Γ`-`Spec` adjunction. -/
theorem ofAugmentation_toAffine {U : X.Opens} {ι : Type u} {P : CommAlgCat.{u} Λ}
    (e : P ≅ CommAlgCat.of Λ (MvPolynomial ι Λ))
    (φ : P ⟶ (openAlgebra Λ X structureMap).obj (op U)) :
    (ofAugmentation e φ).toAffine = openToSpec Λ X structureMap U ≫
      Spec.map ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map φ) := rfl

/-- The structural arrow of `ofAugmentation e φ` over `Spec Λ` is the one induced by the structure
map of the given algebra; in particular it does not depend on the chosen presentation. -/
theorem ofAugmentation_toBase {U : X.Opens} {ι : Type u} {P : CommAlgCat.{u} Λ}
    (e : P ≅ CommAlgCat.of Λ (MvPolynomial ι Λ))
    (φ : P ⟶ (openAlgebra Λ X structureMap).obj (op U)) :
    (ofAugmentation e φ).toBase = Spec.map (CommRingCat.ofHom (algebraMap Λ P)) := by
  change Spec.map ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map e.inv) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : Λ →+* MvPolynomial ι Λ)) = _
  rw [← Spec.map_comp, ofHom_C_comp]

/-- The morphism of polynomial charts attached to a morphism of augmented polynomial algebras
over an inclusion of opens. -/
def homOfAugmentation {U V : X.Opens} (h : U ≤ V) {ι κ : Type u} {P Q : CommAlgCat.{u} Λ}
    {eP : P ≅ CommAlgCat.of Λ (MvPolynomial ι Λ)} {eQ : Q ≅ CommAlgCat.of Λ (MvPolynomial κ Λ)}
    {φ : P ⟶ (openAlgebra Λ X structureMap).obj (op U)}
    {χ : Q ⟶ (openAlgebra Λ X structureMap).obj (op V)}
    (ψ : Q ⟶ P)
    (hψ : ψ ≫ φ = χ ≫ (openAlgebra Λ X structureMap).map (homOfLE h).op) :
    ofAugmentation eP φ ⟶ ofAugmentation eQ χ where
  open_le := h
  affine := Spec.map ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map ψ)
  map_comm := by
    change (openToSpec Λ X structureMap U ≫
          Spec.map ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map φ)) ≫
        Spec.map ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map ψ)
      = X.homOfLE h ≫ openToSpec Λ X structureMap V ≫
        Spec.map ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map χ)
    rw [← Category.assoc (X.homOfLE h), openToSpec_naturality Λ X structureMap h]
    simp only [← Spec.map_comp, ← Functor.map_comp, Category.assoc, hψ]
    rfl
  base_comm := by
    rw [ofAugmentation_toBase, ofAugmentation_toBase]
    change Spec.map ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map ψ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ Q)) = _
    rw [← Spec.map_comp, algebraMap_comp]

/-- The map of affine spaces of `homOfAugmentation h ψ hψ` is the spectrum of `ψ`. -/
@[simp]
theorem homOfAugmentation_affine {U V : X.Opens} (h : U ≤ V) {ι κ : Type u}
    {P Q : CommAlgCat.{u} Λ}
    {eP : P ≅ CommAlgCat.of Λ (MvPolynomial ι Λ)} {eQ : Q ≅ CommAlgCat.of Λ (MvPolynomial κ Λ)}
    {φ : P ⟶ (openAlgebra Λ X structureMap).obj (op U)}
    {χ : Q ⟶ (openAlgebra Λ X structureMap).obj (op V)}
    (ψ : Q ⟶ P)
    (hψ : ψ ≫ φ = χ ≫ (openAlgebra Λ X structureMap).map (homOfLE h).op) :
    (homOfAugmentation h ψ hψ (eP := eP) (eQ := eQ)).affine
      = Spec.map ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map ψ) := rfl

/-! ### The cosimplicial charts of the standard resolution -/

variable (Λ X structureMap)

/-- The standard resolution of `𝒪_X(U)` over `Λ`, functorially in the open `U`. -/
abbrev openStandardResolution : X.Opensᵒᵖ ⥤ SimplicialObject.Augmented (CommAlgCat.{u} Λ) :=
  openAlgebra Λ X structureMap ⋙ CommAlgCat.standardResolutionFunctor.{u, u} Λ

/-- The set of variables of the degree `n` term of the standard resolution of `𝒪_X(U)`. -/
abbrev resolutionVariableIndex (U : X.Opens) (n : SimplexCategory) : Type u :=
  (((CommAlgCat.polynomialComonad.{u, u} Λ).toFunctor.iterate n.len).obj
    ((openAlgebra Λ X structureMap).obj (op U)) : Type u)

/-- The degree `n` term of the standard resolution of `𝒪_X(U)` is a polynomial algebra. -/
def resolutionPresentation (U : X.Opens) (n : SimplexCategory) :
    ((openStandardResolution Λ X structureMap).obj (op U)).left.obj (op n)
      ≅ CommAlgCat.of Λ (MvPolynomial (resolutionVariableIndex Λ X structureMap U n) Λ) :=
  eqToIso (CommAlgCat.standardResolution_obj_mvPolynomial Λ _ n.len)

/-- The functorial cosimplicial polynomial charts of the standard resolutions (the data of Stacks
08VB): the chart in degree `n` over the open `U` is `A_{n,U} = Spec(P_{n,U})` for `P_{•,U}` the
standard resolution of `𝒪_X(U)` over `Λ`, cosimplicial in `n` and functorial in `U`. -/
def standardResolutionChart :
    X.Opens ⥤ CosimplicialObject (PolynomialChart Λ X structureMap) where
  obj U :=
    { obj := fun n => ofAugmentation (resolutionPresentation Λ X structureMap U n)
        (((openStandardResolution Λ X structureMap).obj (op U)).hom.app (op n))
      map := fun {n m} f => homOfAugmentation le_rfl
        (((openStandardResolution Λ X structureMap).obj (op U)).left.map f.op) (by
          have hn := ((openStandardResolution Λ X structureMap).obj (op U)).hom.naturality f.op
          simp only [Functor.id_obj] at hn
          rw [hn, Subsingleton.elim (homOfLE (le_refl U)) (𝟙 U), op_id,
            CategoryTheory.Functor.map_id]
          simp)
      map_id := fun n => by
        ext
        simp only [homOfAugmentation_affine, id_affine, op_id,
          CategoryTheory.Functor.map_id, Spec.map_id]
        rfl
      map_comp := fun f g => by
        ext
        simp only [comp_affine, homOfAugmentation_affine, op_comp,
          CategoryTheory.Functor.map_comp, Spec.map_comp] }
  map {U V} h :=
    { app := fun n => homOfAugmentation (leOfHom h)
        (((openStandardResolution Λ X structureMap).map h.op).left.app (op n)) (by
          have hw := NatTrans.congr_app
            ((openStandardResolution Λ X structureMap).map h.op).w (op n)
          simp only [Functor.id_obj, Functor.id_map, NatTrans.comp_app] at hw
          rw [hw, Subsingleton.elim (homOfLE (leOfHom h)) h]
          simp)
      naturality := fun {n m} f => by
        ext
        simp only [comp_affine, homOfAugmentation_affine]
        rw [← Spec.map_comp, ← Spec.map_comp, ← CategoryTheory.Functor.map_comp,
          ← CategoryTheory.Functor.map_comp,
          ((openStandardResolution Λ X structureMap).map h.op).left.naturality f.op] }
  map_id U := by
    ext n
    have hid : (CommaMorphism.left
        (𝟙 ((openStandardResolution Λ X structureMap).obj (op U)))).app (op n) = 𝟙 _ := rfl
    simp only [NatTrans.id_app, homOfAugmentation_affine, id_affine, op_id, hid,
      CategoryTheory.Functor.map_id, Spec.map_id]
    rfl
  map_comp {U V W} h₁ h₂ := by
    ext n
    have hcomp : ((openStandardResolution Λ X structureMap).map h₂.op ≫
          (openStandardResolution Λ X structureMap).map h₁.op).left.app (op n)
        = ((openStandardResolution Λ X structureMap).map h₂.op).left.app (op n) ≫
          ((openStandardResolution Λ X structureMap).map h₁.op).left.app (op n) := rfl
    simp only [NatTrans.comp_app, comp_affine, homOfAugmentation_affine, op_comp, hcomp,
      CategoryTheory.Functor.map_comp, Spec.map_comp]

/-- The underlying open of every chart of `standardResolutionChart` at `U` is `U`. -/
@[simp]
theorem standardResolutionChart_obj_obj_openPart (U : X.Opens) (n : SimplexCategory) :
    (((standardResolutionChart Λ X structureMap).obj U).obj n).openPart = U := rfl

/-- `A_{•,U}` is a cosimplicial object of the fibre of `C_{X/Λ}` over `U`: composing it with the
forgetful functor to the opens of `X` gives the constant functor at `U`. -/
theorem standardResolutionChart_comp_openFunctor (U : X.Opens) :
    ((standardResolutionChart Λ X structureMap).obj U) ⋙ openFunctor
      = (Functor.const SimplexCategory).obj U :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ => Subsingleton.elim _ _

/-- The standard resolution `P_{•,U}` of `𝒪_X(U)` over `Λ` read as a cosimplicial object
`A_{•,U} = Spec(P_{•,U})` of the fibre category `C_{𝒪_X(U)/Λ}` of `C_{X/Λ}` over `U`, as in
Stacks 08VB. -/
def standardResolutionFibreChart (U : X.Opens) :
    CosimplicialObject
      ((openFunctor (Λ := Λ) (X := X) (structureMap := structureMap)).Fiber U) :=
  Functor.Fiber.inducedFunctor (standardResolutionChart_comp_openFunctor Λ X structureMap U)

/-- Read back in `C_{X/Λ}`, the cosimplicial object of the fibre over `U` is `A_{•,U}`. -/
theorem standardResolutionFibreChart_comp_fiberInclusion (U : X.Opens) :
    standardResolutionFibreChart Λ X structureMap U ⋙ Functor.Fiber.fiberInclusion
      = (standardResolutionChart Λ X structureMap).obj U := rfl

/-- **Stacks 08QI for the sections on an open.** For every open `U` the standard resolution
`P_{•,U} ⟶ 𝒪_X(U)` is a resolution: each term is a polynomial `Λ`-algebra and the augmentation
is a trivial Kan fibration of the underlying simplicial sets. -/
theorem isResolution_openStandardResolution (U : X.Opens) :
    @CommAlgCat.IsResolution Λ _ ((openAlgebra Λ X structureMap).obj (op U))
      ((openAlgebra Λ X structureMap).obj (op U)).commRing
      ((openAlgebra Λ X structureMap).obj (op U)).algebra
      ((openStandardResolution Λ X structureMap).obj (op U)).left
      ((openStandardResolution Λ X structureMap).obj (op U)).hom :=
  CommAlgCat.standardResolution_isResolution.{u, u} Λ _

/-! ### Evaluating a presheaf on the cosimplicial charts -/

variable {Λ X structureMap}

/-- The simplicial presheaf `U ↦ ℱ(A_{•,U})` obtained by evaluating a presheaf `ℱ` on `C_{X/Λ}`
on the functorial cosimplicial charts of the standard resolutions. -/
def standardResolutionEvaluation {A : Type v} [Category.{w} A]
    (F : (PolynomialChart Λ X structureMap)ᵒᵖ ⥤ A) :
    SimplicialObject (X.Opensᵒᵖ ⥤ A) where
  obj n := ((standardResolutionChart Λ X structureMap) ⋙
    (evaluation SimplexCategory (PolynomialChart Λ X structureMap)).obj n.unop).op ⋙ F
  map {n m} f :=
    { app := fun U =>
        F.map (((standardResolutionChart Λ X structureMap).obj U.unop).map f.unop).op
      naturality := fun {U V} g => by
        dsimp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
          Functor.comp_obj, Functor.op_obj, evaluation_obj_map]
        rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp,
          ((standardResolutionChart Λ X structureMap).map g.unop).naturality f.unop] }
  map_id n := by
    ext U
    dsimp only [NatTrans.id_app]
    rw [unop_id, CategoryTheory.Functor.map_id, op_id]
    exact F.map_id _
  map_comp {n m k} f g := by
    ext U
    dsimp only [NatTrans.comp_app]
    rw [unop_comp, CategoryTheory.Functor.map_comp, op_comp, CategoryTheory.Functor.map_comp]

/-- The simplicial presheaf of `standardResolutionEvaluation` is, at each open `U`, the
simplicial object `ℱ(A_{•,U})`. -/
theorem standardResolutionEvaluation_comp_evaluation {A : Type v} [Category.{w} A]
    (F : (PolynomialChart Λ X structureMap)ᵒᵖ ⥤ A) (U : X.Opens) :
    standardResolutionEvaluation F ⋙ (evaluation X.Opensᵒᵖ A).obj (op U)
      = ((standardResolutionChart Λ X structureMap).obj U).op ⋙ F := rfl

/-- The complex of presheaves `U ↦ ℱ(A_{•,U})` of Stacks 08VB attached to a presheaf `ℱ` of
objects of a preadditive category on `C_{X/Λ}`: the alternating face map complex of the
simplicial presheaf obtained by evaluating `ℱ` on the functorial cosimplicial charts of the
standard resolutions. -/
def standardResolutionComplex {A : Type v} [Category.{w} A] [Preadditive A]
    (F : (PolynomialChart Λ X structureMap)ᵒᵖ ⥤ A) :
    ChainComplex (X.Opensᵒᵖ ⥤ A) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (X.Opensᵒᵖ ⥤ A)).obj
    (standardResolutionEvaluation F)

/-- The degree `n` term of the complex of presheaves is `U ↦ ℱ(A_{n,U})`. -/
theorem standardResolutionComplex_X {A : Type v} [Category.{w} A] [Preadditive A]
    (F : (PolynomialChart Λ X structureMap)ᵒᵖ ⥤ A) (n : ℕ) :
    (standardResolutionComplex F).X n
      = ((standardResolutionChart Λ X structureMap) ⋙
        (evaluation SimplexCategory (PolynomialChart Λ X structureMap)).obj ⦋n⦌).op ⋙ F := rfl

end AlgebraicGeometry.PolynomialChart

end

end
