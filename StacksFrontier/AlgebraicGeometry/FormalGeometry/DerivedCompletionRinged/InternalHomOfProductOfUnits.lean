module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingCriterion
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.LocalKernel

/-!
# Internal Hom out of a finite product of copies of the structure sheaf

Let `(𝒞, 𝒪)` be a ringed site and let `ι` be a finite type. A product of `ι` copies of a single
object of a preadditive category is also their coproduct, with the `i`-th inclusion the one whose
`j`-th component is `𝟙` for `j = i` and `0` otherwise. Internal Hom carries coproducts in its
first variable to products ([Stacks, Tag 03EN]), and `𝓗om(𝒪, G) ≅ G`, so

`𝓗om(∏_{i ∈ ι} 𝒪, G) ≅ ∏_{i ∈ ι} G`,

with the `i`-th projection induced by the `i`-th inclusion. At `G = 𝒪` this is the degreewise
collapse of the naive dual of a complex whose terms are finite products of copies of `𝒪`, which
is the shape of the Koszul complex in the alternating Čech model: its term in degree `p` is the
product of copies of `𝒪` indexed by the subsets of `Fin r` of cardinality `p`.

## Main definitions

* `CategoryTheory.Limits.piConstι`: the `i`-th inclusion of `A` into a product of copies of `A`.
* `CategoryTheory.Limits.isColimitCofanPiConst`: a finite product of copies of one object of a
  preadditive category is their coproduct along those inclusions.
* `AlgebraicGeometry.RingedSite.isLimitFanInternalHomPiUnit`: `𝓗om(∏_ι 𝒪, G)` is the product of
  `ι` copies of `𝓗om(𝒪, G)`.
* `AlgebraicGeometry.RingedSite.internalHomPiUnitIso`: **`𝓗om(∏_ι 𝒪, G) ≅ ∏_ι G`.**
* `CategoryTheory.Limits.piConstTranspose`: the transpose of a morphism between finite products
  of copies of one object, read as a matrix of endomorphisms.

## Main results

* `AlgebraicGeometry.RingedSite.internalHomPiUnitIso_hom_comp_π`: the characterising clause of
  `internalHomPiUnitIso` — its `i`-th component is precomposition with the `i`-th inclusion,
  followed by the trivialisation `𝓗om(𝒪, G) ≅ G`.
* `CategoryTheory.Limits.sum_π_comp_piConstι`: the total relation, that the projections followed
  by the inclusions sum to the identity.
* `AlgebraicGeometry.RingedSite.internalHomPre_comp_internalHomPiUnitIso_hom`:
  **`internalHomPiUnitIso` transposes a matrix of endomorphisms of `𝒪`.** This is what says that
  the differential of the naive dual of a complex of finite products of copies of `𝒪` is the
  transposed matrix; at the Koszul complex it is the Koszul contraction.
* `CategoryTheory.Limits.piConstTranspose_piMap`: a diagonal morphism is its own transpose.

## Implementation notes

**What the transpose needs beyond `internalHomPiUnitIso_hom_comp_π`.** The clause expresses the
`i`-th component through the trivialisation `𝓗om(𝒪, G) ≅ G`, so the transposition is not a
formal consequence of the clause and the total relation alone: it also needs that the
trivialisation *intertwines precomposition with an endomorphism of `𝒪` and that endomorphism*,
`internalHomPre_comp_unitSheafInternalHomIso_hom`. The trivialisation is natural in its second
variable for free, being the component of a functor isomorphism, and the first variable is
reduced to the second by `internalHomPre_unit_eq_internalHomPost`: a section of `𝓗om(𝒪, 𝒪)` over
`U` is an `𝒪|_U`-linear endomorphism of the free rank-one module `𝒪|_U`, hence multiplication by
its value at `1`, so precomposing with `e` and postcomposing with `e` agree because `𝒪` is
commutative. This is the one input that is genuine content rather than bookkeeping, and it is
where commutativity of `𝒪` enters the self-duality of the Koszul complex.

The transposition computation itself is carried out against an abstract morphism standing for
the trivialisation. The trivialisation is stated for
`Stacks.SheafOfModules.InternalHom.sheafInternalHom`, which is the same sheaf of modules as
`internalHomSheaf` only up to unfolding a non-reducible definition, so a composite built around
it is not type-correct at the transparency at which `rw` rebuilds a term; against a variable it
is, and the use site applies the result as a term.

The one-factor case `𝓗om(𝒪, G) ≅ G` is
`Stacks.SheafOfModules.InternalHom.unitSheafInternalHomIso`, stated for the `abbrev`
`Stacks.SheafOfModules.InternalHom.sheafInternalHom`, which is the same sheaf of modules as
`AlgebraicGeometry.RingedSite.internalHomSheaf` by `rfl`.

The index type carries `DecidableEq` rather than deciding equality classically, because the
inclusions are used in `simp`-normal form downstream, where a classical `Decidable` instance
would not match the one arising from the `Finset` structure of the Koszul index type.

The index type of the internal-Hom statement is in `Type`, not in the module universe: finite
products in a category with `CategoryTheory.Limits.HasFiniteProducts` are indexed by types of
`Type`, and the index type this is applied to — the `p`-element subsets of `Fin r`, the index
set of the degree-`p` term of the Koszul complex in the alternating Čech model — is one. This
matches `AlgebraicGeometry.RingedSite.isFiniteFreeSummand_pi_unit`, which is stated at the same
index universe for the same reason.

`isColimitCofanPiConst` is stated for a constant family, not for a general family with a
biproduct: the constant case is the only one needed, and it avoids the `eqToHom (congrArg F h)`
of `CategoryTheory.Limits.Bicone.ι_π` leaking into the inclusions.

## References

* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

/-- An element of a semiring is itself times the unit, read as a scalar action. Stated separately
from `smul_eq_mul` so that it applies, up to definitional unfolding, to the module structure that
`PresheafOfModules.unit` carries on the sections of the structure sheaf. -/
private theorem eq_smul_one {R : Type*} [Semiring R] (m : R) : m = m • (1 : R) := by
  rw [smul_eq_mul, mul_one]

/-- **Two linear endomorphisms of a cyclic module commute**, provided the scalars commute: each
such endomorphism is multiplication by its value on the generator. -/
private theorem linearEnd_comm {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] (u : M) (hu : ∀ m : M, ∃ s : R, m = s • u)
    (hcomm : ∀ s t : R, s * t = t * s) (φ ψ : M →ₗ[R] M) (y : M) :
    φ (ψ y) = ψ (φ y) := by
  obtain ⟨s, hs⟩ := hu (φ u)
  obtain ⟨t, ht⟩ := hu (ψ u)
  have h1 : φ (ψ u) = ψ (φ u) := by
    rw [ht, map_smul, hs, map_smul, ht, smul_smul, smul_smul, hcomm]
  obtain ⟨c, rfl⟩ := hu y
  rw [map_smul, map_smul, map_smul, map_smul, h1]

namespace CategoryTheory.Limits

universe w v u

section Const

variable {C : Type u} [Category.{v} C] [Preadditive C] {J : Type w} [DecidableEq J]
  (A : C) [HasProduct fun _ : J => A]

/-- **The `j`-th inclusion of `A` into a product of copies of `A`.** Its `j'`-th component is the
identity for `j' = j` and zero otherwise. -/
def piConstι (j : J) : A ⟶ ∏ᶜ fun _ : J => A :=
  Pi.lift fun j' => if j = j' then 𝟙 A else 0

/-- The `j'`-th component of `piConstι A j` is the identity if `j = j'` and zero otherwise. -/
@[reassoc]
lemma piConstι_comp_π (j j' : J) :
    piConstι A j ≫ Pi.π (fun _ : J => A) j' = if j = j' then 𝟙 A else 0 :=
  Pi.lift_comp_π _ _

/-- The `j`-th component of `piConstι A j` is the identity. -/
@[simp]
lemma piConstι_comp_π_self (j : J) :
    piConstι A j ≫ Pi.π (fun _ : J => A) j = 𝟙 A := by
  rw [piConstι_comp_π, if_pos rfl]

/-- The `j'`-th component of `piConstι A j` is zero when `j ≠ j'`. -/
lemma piConstι_comp_π_of_ne {j j' : J} (h : j ≠ j') :
    piConstι A j ≫ Pi.π (fun _ : J => A) j' = 0 := by
  rw [piConstι_comp_π, if_neg h]

/-- A product of copies of `A`, with the projections and the inclusions `piConstι`, as a
bicone on the constant family. -/
def biconeConst : Bicone fun _ : J => A where
  pt := ∏ᶜ fun _ : J => A
  π := Pi.π _
  ι := piConstι A
  ι_π j j' := by
    rw [piConstι_comp_π]
    by_cases h : j = j' <;> simp [h]

/-- The cone point of `biconeConst A` is the product of copies of `A`. -/
@[simp] lemma biconeConst_pt : (biconeConst (J := J) A).pt = ∏ᶜ fun _ : J => A := rfl

/-- The projections of `biconeConst A` are the product projections. -/
@[simp] lemma biconeConst_π (j : J) : (biconeConst (J := J) A).π j = Pi.π _ j := rfl

/-- The inclusions of `biconeConst A` are the maps `piConstι A j`. -/
@[simp] lemma biconeConst_ι (j : J) : (biconeConst (J := J) A).ι j = piConstι A j := rfl

/-- A finite product of copies of one object of a preadditive category, with the projections and
the inclusions `CategoryTheory.Limits.piConstι`, is a biproduct. -/
def isBilimitBiconeConst [Fintype J] : (biconeConst (J := J) A).IsBilimit :=
  isBilimitOfIsLimit (biconeConst (J := J) A)
    (IsLimit.ofIsoLimit (productIsProduct fun _ : J => A)
      (Cone.ext (Iso.refl _) (fun j => by cases j; simp)))

/-- **A finite product of copies of one object of a preadditive category is their coproduct**,
along the inclusions `CategoryTheory.Limits.piConstι`. -/
def isColimitCofanPiConst [Fintype J] :
    IsColimit (Cofan.mk (∏ᶜ fun _ : J => A) (piConstι (J := J) A)) :=
  IsColimit.ofIsoColimit (isBilimitBiconeConst A).isColimit
    (Cocone.ext (Iso.refl _) (fun j => by cases j; simp))

/-- **The total relation of a finite product of copies of one object**: the projections followed
by the inclusions `CategoryTheory.Limits.piConstι` sum to the identity. -/
lemma sum_π_comp_piConstι [Fintype J] :
    ∑ j : J, Pi.π (fun _ : J => A) j ≫ piConstι A j = 𝟙 (∏ᶜ fun _ : J => A) :=
  IsBilimit.total (isBilimitBiconeConst A)

end Const

section Transpose

variable {C : Type u} [Category.{v} C] [Preadditive C] {J K : Type w} [DecidableEq J]
  (A : C) [HasProduct fun _ : J => A] [HasProduct fun _ : K => A] [Fintype K]

/-- **The transpose of a morphism between finite products of copies of one object.** A morphism
`∏_J A ⟶ ∏_K A` is a matrix of endomorphisms of `A`, its `(k, j)` entry being
`piConstι A j ≫ g ≫ Pi.π k`; the transpose is the morphism `∏_K A ⟶ ∏_J A` whose matrix is the
same entries read the other way, that is, whose component at `j` is the sum over `k` of the
`(k, j)` entry after the `k`-th projection. -/
def piConstTranspose (g : (∏ᶜ fun _ : J => A) ⟶ ∏ᶜ fun _ : K => A) :
    (∏ᶜ fun _ : K => A) ⟶ ∏ᶜ fun _ : J => A :=
  Pi.lift fun j => ∑ k : K, Pi.π (fun _ : K => A) k ≫
    (piConstι A j ≫ g ≫ Pi.π (fun _ : K => A) k)

/-- The component of `CategoryTheory.Limits.piConstTranspose` at an index of the target. -/
@[reassoc]
lemma piConstTranspose_comp_π (g : (∏ᶜ fun _ : J => A) ⟶ ∏ᶜ fun _ : K => A) (j : J) :
    piConstTranspose A g ≫ Pi.π (fun _ : J => A) j =
      ∑ k : K, Pi.π (fun _ : K => A) k ≫
        (piConstι A j ≫ g ≫ Pi.π (fun _ : K => A) k) :=
  Pi.lift_comp_π _ _

/-- **A diagonal morphism is its own transpose.** The `(k, j)` entry of
`CategoryTheory.Limits.Pi.map e` is `e j` for `k = j` and zero otherwise, a matrix symmetric in
its two indices. This is what makes the transition map of the Koszul tower its own transpose. -/
lemma piConstTranspose_piMap [Fintype J] (e : J → (A ⟶ A)) :
    piConstTranspose (K := J) A (Pi.map fun j => e j) = Pi.map fun j => e j := by
  refine Pi.hom_ext _ _ fun j => ?_
  simp [piConstTranspose_comp_π, piConstι_comp_π_assoc, ite_comp, comp_ite]

end Transpose

end CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ι : Type) [Fintype ι] [DecidableEq ι]

/-- **Internal Hom out of a finite product of copies of the structure sheaf is a product.** The
product of `ι` copies of `𝒪` is their coproduct, and [Stacks, Tag 03EN] in the first variable
carries that coproduct to the product of `ι` copies of `𝓗om(𝒪, G)`, with the projections induced
by the inclusions. -/
def isLimitFanInternalHomPiUnit :
    IsLimit (Fan.mk
      (internalHomSheaf X
        (∏ᶜ fun _ : ι => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) G)
      fun i : ι => internalHomPre X (C := G)
        (piConstι (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i)) :=
  isLimitFanOfIsColimitCofanOp _
    ((Cofan.isColimitMapCoconeEquiv
        (Stacks.SheafOfModules.InternalHom.internalHomFirstFunctor X G) _
        (Cofan.mk _ (piConstι (J := ι)
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))))
      (isColimitOfPreserves (Stacks.SheafOfModules.InternalHom.internalHomFirstFunctor X G)
        (isColimitCofanPiConst (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))))

/-- The same fan with the trivialisation `𝓗om(𝒪, G) ≅ G` applied to each projection: a limit fan
on the constant family at `G`. -/
def isLimitFanInternalHomPiUnitTriv :
    IsLimit (Fan.mk
      (internalHomSheaf X
        (∏ᶜ fun _ : ι => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) G)
      fun i : ι => internalHomPre X (C := G)
          (piConstι (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i) ≫
        (Stacks.SheafOfModules.InternalHom.unitSheafInternalHomIso X G).hom) :=
  isLimitFanCompIso (isLimitFanInternalHomPiUnit X G ι)
    fun _ => Stacks.SheafOfModules.InternalHom.unitSheafInternalHomIso X G

/-- **`𝓗om(∏_{i ∈ ι} 𝒪, G) ≅ ∏_{i ∈ ι} G` for a finite index type.** -/
def internalHomPiUnitIso :
    internalHomSheaf X
        (∏ᶜ fun _ : ι => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) G ≅
      ∏ᶜ fun _ : ι => G :=
  IsLimit.conePointUniqueUpToIso (isLimitFanInternalHomPiUnitTriv X G ι)
    (productIsProduct fun _ : ι => G)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The characterising clause of `internalHomPiUnitIso`.** Its `i`-th component is
precomposition with the `i`-th inclusion of `𝒪` into the product, followed by the trivialisation
`𝓗om(𝒪, G) ≅ G`. -/
@[reassoc]
theorem internalHomPiUnitIso_hom_comp_π (i : ι) :
    (internalHomPiUnitIso X G ι).hom ≫ Pi.π (fun _ : ι => G) i =
      internalHomPre X (C := G)
          (piConstι (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i) ≫
        (Stacks.SheafOfModules.InternalHom.unitSheafInternalHomIso X G).hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isLimitFanInternalHomPiUnitTriv X G ι)
    (productIsProduct fun _ : ι => G) ⟨i⟩

/-! ### Transposition of a matrix of endomorphisms of the structure sheaf -/

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Precomposition on internal Hom sheaves carries a finite sum of morphisms to the sum of the
precompositions: it is additive, and `CategoryTheory.Limits.piConstTranspose` is a sum. -/
lemma internalHomPre_sum {A B C : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {σ : Type*} (s : Finset σ)
    (φ : σ → (A ⟶ B)) :
    internalHomPre X (C := C) (∑ i ∈ s, φ i) = ∑ i ∈ s, internalHomPre X (C := C) (φ i) :=
  map_sum (AddMonoidHom.mk' (fun ψ => internalHomPre X (C := C) ψ) (internalHomPre_add X)) φ s

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Precomposition and postcomposition on `𝓗om(𝒪, 𝒪)` agree at an endomorphism of `𝒪`.**
A section of `𝓗om(𝒪, G)` over `U` is an `𝒪|_U`-linear map out of the free rank-one module
`𝒪|_U`, hence multiplication by its value at `1`; two such maps therefore commute because `𝒪` is
commutative, and precomposing a section with `e` is the same as postcomposing it with `e`. -/
theorem internalHomPre_unit_eq_internalHomPost
    (e : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomPre X (C := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) e =
      internalHomPost X (A := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        e := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun a => ?_))
  refine PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  have hpre :
      ((internalHomPre X (C := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          e).val.app U a).app W y =
        a.app W (e.val.app (op (unop W).left) y) := by with_unfolding_all rfl
  have hpost :
      ((internalHomPost X (A := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          e).val.app U a).app W y =
        e.val.app (op (unop W).left) (a.app W y) := by with_unfolding_all rfl
  rw [hpre, hpost]
  exact linearEnd_comm
    (show ((restrFun X.O.obj (unop U)).obj
      (X.valOf (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj W from
        (1 : (ORestr X.O.obj (unop U)).obj W))
    (fun m => ⟨show (ORestr X.O.obj (unop U)).obj W from m,
      eq_smul_one (show (ORestr X.O.obj (unop U)).obj W from m)⟩)
    (fun s t => mul_comm (G := X.O.obj.obj (op (unop W).left)) s t)
    (ModuleCat.Hom.hom (a.app W)) (ModuleCat.Hom.hom (e.val.app (op (unop W).left))) y

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The trivialisation `𝓗om(𝒪, G) ≅ G` is natural in `G`.** This is the naturality of
`Stacks.SheafOfModules.InternalHom.unitInternalHomFunctorIso`, whose second-variable functor has
`Stacks.PresheafOfModules.InternalHom.internalHomMapRight` — the underlying presheaf morphism of
`AlgebraicGeometry.RingedSite.internalHomPost` — for its action on morphisms. -/
@[reassoc]
theorem internalHomPost_comp_unitSheafInternalHomIso_hom
    {G₁ G₂ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (h : G₁ ⟶ G₂) :
    internalHomPost X (A := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) h ≫
        (Stacks.SheafOfModules.InternalHom.unitSheafInternalHomIso X G₂).hom =
      (Stacks.SheafOfModules.InternalHom.unitSheafInternalHomIso X G₁).hom ≫ h :=
  SheafOfModules.hom_ext
    ((Stacks.SheafOfModules.InternalHom.unitInternalHomFunctorIso X.O.obj).inv.naturality h.val)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The trivialisation `𝓗om(𝒪, 𝒪) ≅ 𝒪` intertwines precomposition with an endomorphism of `𝒪`
and that endomorphism itself.** Precomposition agrees with postcomposition here by
`internalHomPre_unit_eq_internalHomPost`, and postcomposition is intertwined by naturality. -/
@[reassoc]
theorem internalHomPre_comp_unitSheafInternalHomIso_hom
    (e : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomPre X (C := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) e ≫
        (Stacks.SheafOfModules.InternalHom.unitSheafInternalHomIso X
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom =
      (Stacks.SheafOfModules.InternalHom.unitSheafInternalHomIso X
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom ≫ e := by
  rw [internalHomPre_unit_eq_internalHomPost]
  exact internalHomPost_comp_unitSheafInternalHomIso_hom X e

section Transpose

variable (κ : Type) [Fintype κ] [DecidableEq κ]

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The transposition computation, with the trivialisation `𝓗om(𝒪, 𝒪) ≅ 𝒪` abstracted as a
morphism `w` out of `internalHomSheaf X 𝒪 𝒪` together with the two properties of it that the
computation uses. Abstracting it is what makes the associativity rearrangements go through: the
trivialisation is stated for `Stacks.SheafOfModules.InternalHom.sheafInternalHom`, which is the
same sheaf of modules as `AlgebraicGeometry.RingedSite.internalHomSheaf` only up to unfolding a
non-reducible definition, so a composite built around it is not type-correct at the transparency
at which `rw` rebuilds a term. Against a variable `w` it is. -/
private lemma piConstTranspose_aux
    (w : internalHomSheaf X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hw : ∀ e : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      internalHomPre X (C := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        e ≫ w = w ≫ e)
    (hι : ∀ i : ι, (internalHomPiUnitIso X
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ι).hom ≫
        Pi.π (fun _ : ι => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i =
      internalHomPre X (C := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (piConstι (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i) ≫ w)
    (hκ : ∀ k : κ, (internalHomPiUnitIso X
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) κ).hom ≫
        Pi.π (fun _ : κ => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k =
      internalHomPre X (C := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (piConstι (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k) ≫ w)
    (g : (∏ᶜ fun _ : ι => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
      ∏ᶜ fun _ : κ => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomPre X (C := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) g ≫
        (internalHomPiUnitIso X
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ι).hom =
      (internalHomPiUnitIso X
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) κ).hom ≫
        piConstTranspose (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) g := by
  refine Pi.hom_ext _ _ fun i => ?_
  have htotal :
      (∑ k : κ, (piConstι (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i ≫
        g ≫
        Pi.π (fun _ : κ => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k) ≫
          piConstι (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k) =
      piConstι (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i ≫ g := by
    calc (∑ k : κ, (piConstι (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i ≫
            g ≫
            Pi.π (fun _ : κ => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              k) ≫
              piConstι (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k)
        = (piConstι (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i ≫ g) ≫
            ∑ k : κ,
              Pi.π (fun _ : κ => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
                k ≫
                piConstι (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k := by
          rw [Preadditive.comp_sum]
          exact Finset.sum_congr rfl fun k _ => by simp only [Category.assoc]
      _ = piConstι (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i ≫ g := by
          rw [sum_π_comp_piConstι, Category.comp_id]
  rw [Category.assoc, hι, Category.assoc, piConstTranspose_comp_π, Preadditive.comp_sum,
    ← Category.assoc, internalHomPre_comp, ← htotal, internalHomPre_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← internalHomPre_comp, Category.assoc, hw, ← Category.assoc, ← hκ]
  exact Category.assoc _ _ _

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **`internalHomPiUnitIso` transposes a matrix of endomorphisms of `𝒪`.** A morphism
`g : ∏_ι 𝒪 ⟶ ∏_κ 𝒪` is a matrix of endomorphisms of `𝒪`, its `(k, i)` entry being
`piConstι i ≫ g ≫ Pi.π k`. Precomposition with `g` on internal Homs into `𝒪`, read through
`internalHomPiUnitIso` at both ends, is the transposed matrix
`CategoryTheory.Limits.piConstTranspose`.

The proof is the total relation `CategoryTheory.Limits.sum_π_comp_piConstι`, which expands
`piConstι i ≫ g` as the sum over `k` of its `(k, i)` entry followed by the `k`-th inclusion,
together with the additivity and the contravariant functoriality of `internalHomPre` and the
intertwining `internalHomPre_comp_unitSheafInternalHomIso_hom`. -/
theorem internalHomPre_comp_internalHomPiUnitIso_hom
    (g : (∏ᶜ fun _ : ι => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
      ∏ᶜ fun _ : κ => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomPre X (C := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) g ≫
        (internalHomPiUnitIso X
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ι).hom =
      (internalHomPiUnitIso X
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) κ).hom ≫
        piConstTranspose (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) g :=
  piConstTranspose_aux X ι κ
    (Stacks.SheafOfModules.InternalHom.unitSheafInternalHomIso X
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom
    (internalHomPre_comp_unitSheafInternalHomIso_hom X)
    (internalHomPiUnitIso_hom_comp_π X
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ι)
    (internalHomPiUnitIso_hom_comp_π X
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) κ) g

end Transpose

end AlgebraicGeometry.RingedSite

end
