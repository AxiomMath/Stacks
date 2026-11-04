module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulSheafDifferential
public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.CoordinateContraction

/-!
# Koszul contractions on an arbitrary exterior algebra of a sheaf of modules

Let `O♯` be a sheaf of commutative rings on a site `(C, J)` and let `F` be a sheaf of
`O♯`-modules. The Koszul differential of a functional `φ` on `F` is built in
`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.SheafifiedDifferential` on the homogeneous pieces of
`SheafOfModules.sheafifiedExteriorAlgebra J F`, the exterior algebra realized as the degreewise
sheafification of the sectionwise exterior algebra. A statement about *the* exterior algebra of
`F` is instead phrased for an arbitrary graded algebra `A` with a degree-one generator having the
universal property, `SheafOfModules.GradedAlgebra.IsExteriorAlgebra A gen`; the homogeneous
pieces of such an `A` are not the homogeneous pieces of the realized algebra, and are identified
with them only by the canonical degreewise isomorphism that the universal property produces.

This file carries the Koszul differentials across that identification. For each `n` there is one
isomorphism `⋀ⁿ(F) ≅ A.piece n` compatible with the generators, the products and the units, and
conjugating by it transports every degree `-1` operator on the realized algebra to one on `A`.
Conjugation by an isomorphism is additive and multiplicative for composition, so **no sign
changes**: the transported operators satisfy the anticommutation and squaring identities they
satisfied before, verbatim.

Three layers are provided, each a definitional specialization of the previous one, so that a
consumer of the last never mentions the identification:

* on the pieces of an arbitrary exterior algebra `A` of `F`, given the universal property;
* on the exterior powers `A.exterior.piece n` of a bundle of tensor, exterior and symmetric
  algebras `A` of `F`, where the universal property is one of the bundle's fields;
* on the terms `K.chain.X n` of the Koszul chain complex of
  `Stacks.RegularSequence.KoszulChainData`, whose degree-`n` term is the degree-`n` exterior power
  up to the equality of objects `chain_X`.

Specializing the functional to the `j`-th coordinate functional of a finite free sheaf of modules
gives the contractions `δⱼ` of
`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.CoordinateContraction` on each of the three.

## Main definitions

* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.sheafifiedPieceIso`: **the canonical degreewise
  isomorphism** from the homogeneous pieces of the realized exterior algebra `⋀(F)` to those of
  an arbitrary exterior algebra of `F`.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.koszulD`: **the Koszul differential of a
  functional on an arbitrary exterior algebra of `F`**, and
  `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.coordKoszulD`: **the contraction `δⱼ` by the
  `j`-th coordinate functional** when `F` is free on a finite index type.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.koszulD` and `coordKoszulD`: the same two
  operators on the exterior powers of a bundle of algebras.
* `Stacks.RegularSequence.KoszulChainData.koszulD` and `coordKoszulD`: the same two operators on
  the terms of the Koszul chain complex, together with
  `Stacks.RegularSequence.KoszulChainData.chainXIso`, the identification of a term of the complex
  with an exterior power.

## Main results

* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.sheafifiedPieceIso_generator`,
  `sheafifiedPieceIso_mul` and `sheafifiedPieceIso_one`: the comparison isomorphism carries one
  degree-one generator to the other, is multiplicative on homogeneous local sections, and carries
  the unit to the unit. These are what make it canonical, hence the transport canonical.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.sheafifiedPieceIso_hom_comp_koszulD`: the
  comparison isomorphism intertwines the realized Koszul differential with the transported one,
  which together with the isomorphism determines the latter.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.koszulD_comp_koszulD` and
  `koszulD_comp_koszulD_comm`: **the transported Koszul differential of a functional squares to
  zero, and the transported differentials of two functionals anticommute.**
* `coordKoszulD_comp_coordKoszulD_comm`, `coordKoszulD_comp_coordKoszulD_self`,
  `coordKoszulD_comp_koszulD_comm` and `koszulD_comp_coordKoszulD_comm`: **the four commutation
  identities of the coordinate contractions**, `δⱼ δₖ = - δₖ δⱼ`, `δⱼ δⱼ = 0` and
  `δⱼ d_φ = - d_φ δⱼ` in either order, each stated on an arbitrary exterior algebra, on the
  exterior powers of a bundle of algebras, and on the terms of the Koszul chain complex.

## Implementation notes

**Conjugation, not re-derivation.** The identities are not reproved for the transported
operators. `Stacks.iso_conj_comp` turns a composite of two conjugated morphisms into the
conjugate of the composite, `Stacks.iso_conj_neg` and `Stacks.iso_conj_zero` move a negation and a
zero across a conjugation, and each identity is then its untransported counterpart with those
three rewrites around it. This is why the signs are literally the same ones: the sign lives in the
preadditive structure of the category of sheaves of modules, which conjugation by an isomorphism
respects.

**Why the second and third layers are definitional.** The exterior algebra of a bundle carries
the universal property as the field `exterior_isExteriorAlgebra`, so the bundle-level operators
are the first layer at that field and the bundle-level identities are the first-layer ones with
no proof at all. The chain-level operators do need one further conjugation, by the equality of
objects `Stacks.RegularSequence.KoszulChainData.chain_X`, read as an isomorphism through
`CategoryTheory.eqToIso`; the same three rewrites handle it.

**Anticommutation with the complex's own differential is not asserted.**
`Stacks.RegularSequence.KoszulChainData` takes the degree-lowering morphisms as data, with only
the graded Leibniz rule and the value on a degree-one generator imposed, and neither identifies
them with the Koszul differential of a functional on `F`; so no identity relating `δⱼ` to the
field `d` is available here. What is available, and is stated, is anticommutation of `δⱼ` with the
transported Koszul differential of an arbitrary functional, which is the identity
`δⱼ d_φ + d_φ δⱼ = 0` for every `φ` whatsoever.

**The free index type.** The coordinate functionals require the index type to be finite with
decidable equality, since they are the coordinate forms of
`Stacks.SheafOfModules.freeCoordBasis`. The index type lives in the universe of the sections,
`ι : Type w`, as it does in `Stacks.SheafOfModules.coordKoszulD`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 062L](https://stacks.math.columbia.edu/tag/062L)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Opposite

universe v u w

namespace Stacks

/-! ### Conjugating a morphism by isomorphisms of its source and target -/

section Conjugation

variable {V : Type u} [Category.{v} V]

/-- Conjugation by isomorphisms is compatible with composition: a conjugated morphism followed by
a conjugated morphism is the conjugate of the composite, the two inner isomorphisms cancelling. -/
theorem iso_conj_comp {X Y Z X' Y' Z' : V} (e : X ≅ X') (e' : Y ≅ Y') (e'' : Z ≅ Z')
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (e.inv ≫ f ≫ e'.hom) ≫ e'.inv ≫ g ≫ e''.hom = e.inv ≫ (f ≫ g) ≫ e''.hom := by
  simp

variable [Preadditive V]

/-- Conjugation by isomorphisms is additive, hence commutes with negation: a sign survives a
transport unchanged. -/
theorem iso_conj_neg {X Y X' Y' : V} (e : X ≅ X') (e' : Y ≅ Y') (f : X ⟶ Y) :
    e.inv ≫ (-f) ≫ e'.hom = -(e.inv ≫ f ≫ e'.hom) := by
  simp

/-- The conjugate of the zero morphism is zero. -/
theorem iso_conj_zero {X Y X' Y' : V} (e : X ≅ X') (e' : Y ≅ Y') :
    e.inv ≫ (0 : X ⟶ Y) ≫ e'.hom = 0 := by
  simp

/-- A conjugated composite of morphisms whose composite is zero is zero. -/
private theorem iso_conj_comp_eq_zero {X Y Z X' Y' Z' : V} (e : X ≅ X') (e' : Y ≅ Y')
    (e'' : Z ≅ Z') {f : X ⟶ Y} {g : Y ⟶ Z} (h : f ≫ g = 0) :
    (e.inv ≫ f ≫ e'.hom) ≫ e'.inv ≫ g ≫ e''.hom = 0 := by
  simp [reassoc_of% h]

/-- Anticommutation of two composites persists after conjugating by isomorphisms. -/
private theorem iso_conj_comp_comm {X Y Z X' Y' Z' : V} (e : X ≅ X') (e' : Y ≅ Y')
    (e'' : Z ≅ Z') {f₁ f₂ : X ⟶ Y} {g₁ g₂ : Y ⟶ Z} (h : f₁ ≫ g₂ = -(f₂ ≫ g₁)) :
    (e.inv ≫ f₁ ≫ e'.hom) ≫ e'.inv ≫ g₂ ≫ e''.hom =
      -((e.inv ≫ f₂ ≫ e'.hom) ≫ e'.inv ≫ g₁ ≫ e''.hom) := by
  simp [reassoc_of% h]

end Conjugation

end Stacks

namespace SheafOfModules.GradedAlgebra.IsExteriorAlgebra

/-! ### The comparison with the realized exterior algebra -/

section Comparison

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F : SheafOfModules.{w} (toRingCat J Osharp)}
  {A : GradedAlgebra.{w, w} (toRingCat J Osharp)} {gen : F ⟶ A.piece 1}

/-- **The canonical degreewise isomorphism** from the homogeneous pieces of the realized exterior
algebra `⋀(F)` — the degreewise sheafification of the sectionwise exterior algebra — to the
homogeneous pieces of an arbitrary exterior algebra `A` of `F`. It is the comparison the universal
property produces from the two degree-one generators. -/
def sheafifiedPieceIso (hA : IsExteriorAlgebra A gen) (n : ℤ) :
    (sheafifiedExteriorAlgebra J F).piece n ≅ A.piece n :=
  (isExteriorAlgebra_sheafifiedExteriorAlgebra J F).pieceIso hA n

/-- The comparison isomorphism carries the degree-one generator of the realized exterior algebra
to the degree-one generator of `A`. -/
theorem sheafifiedPieceIso_generator (hA : IsExteriorAlgebra A gen) :
    sheafifiedExteriorGenerator J F ≫ (hA.sheafifiedPieceIso 1).hom = gen :=
  pieceIso_generator (isExteriorAlgebra_sheafifiedExteriorAlgebra J F) hA

/-- The comparison isomorphism is multiplicative on homogeneous local sections. -/
theorem sheafifiedPieceIso_mul (hA : IsExteriorAlgebra A gen) (i j : ℤ) (U : Cᵒᵖ)
    (x : ((sheafifiedExteriorAlgebra J F).piece i).val.obj U)
    (y : ((sheafifiedExteriorAlgebra J F).piece j).val.obj U) :
    ((hA.sheafifiedPieceIso (i + j)).hom).val.app U
        (((sheafifiedExteriorAlgebra J F).mul i j).app U x y) =
      (A.mul i j).app U (((hA.sheafifiedPieceIso i).hom).val.app U x)
        (((hA.sheafifiedPieceIso j).hom).val.app U y) :=
  IsUniversal.pieceIso_mul (isExteriorAlgebra_sheafifiedExteriorAlgebra J F).isUniversal
    hA.isUniversal i j U x y

/-- The comparison isomorphism carries the unit of the realized exterior algebra to the unit
of `A`. -/
theorem sheafifiedPieceIso_one (hA : IsExteriorAlgebra A gen) (U : Cᵒᵖ) :
    ((hA.sheafifiedPieceIso 0).hom).val.app U ((sheafifiedExteriorAlgebra J F).one.eval U) =
      A.one.eval U :=
  IsUniversal.pieceIso_one (isExteriorAlgebra_sheafifiedExteriorAlgebra J F).isUniversal
    hA.isUniversal U

/-! ### The Koszul differential of a functional, transported -/

/-- **The Koszul differential of a functional `φ` on an arbitrary exterior algebra of `F`**, from
the homogeneous piece of degree `p` to the one of degree `q`, for degrees with `q + 1 = p`. It is
the Koszul differential of Stacks tag 062K on the realized exterior algebra, conjugated by the
canonical degreewise comparison. -/
def koszulD (hA : IsExteriorAlgebra A gen)
    (φ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val) {p q : ℤ} (h : q + 1 = p) :
    A.piece p ⟶ A.piece q :=
  (hA.sheafifiedPieceIso p).inv ≫ _root_.SheafOfModules.koszulD J F φ h ≫
    (hA.sheafifiedPieceIso q).hom

/-- **The comparison isomorphism intertwines the two Koszul differentials.** Since it is an
isomorphism, this identity characterizes the transported differential. -/
theorem sheafifiedPieceIso_hom_comp_koszulD (hA : IsExteriorAlgebra A gen)
    (φ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val) {p q : ℤ} (h : q + 1 = p) :
    (hA.sheafifiedPieceIso p).hom ≫ hA.koszulD φ h =
      _root_.SheafOfModules.koszulD J F φ h ≫ (hA.sheafifiedPieceIso q).hom := by
  simp only [koszulD, Iso.hom_inv_id_assoc]

/-- **The transported Koszul differential of a functional squares to zero.** -/
theorem koszulD_comp_koszulD (hA : IsExteriorAlgebra A gen)
    (φ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val) {p q r : ℤ} (h : q + 1 = p)
    (h' : r + 1 = q) : hA.koszulD φ h ≫ hA.koszulD φ h' = 0 := by
  exact Stacks.iso_conj_comp_eq_zero _ _ _ (_root_.SheafOfModules.koszulD_comp_koszulD J F φ h h')

/-- **The transported Koszul differentials of two functionals anticommute**,
`d_ψ d_φ = - d_φ d_ψ`. The sign is the one of
`SheafOfModules.koszulD_comp_koszulD_comm`: conjugation by an isomorphism is additive. -/
theorem koszulD_comp_koszulD_comm (hA : IsExteriorAlgebra A gen)
    (φ ψ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val) {p q r : ℤ} (h : q + 1 = p)
    (h' : r + 1 = q) :
    hA.koszulD ψ h ≫ hA.koszulD φ h' = -(hA.koszulD φ h ≫ hA.koszulD ψ h') := by
  exact Stacks.iso_conj_comp_comm _ _ _
    (_root_.SheafOfModules.koszulD_comp_koszulD_comm J F φ ψ h h')

end Comparison

/-! ### The coordinate contractions of a finite free sheaf of modules, transported -/

section Coordinates

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {ι : Type w} [DecidableEq ι] [Finite ι]
  {A : GradedAlgebra.{w, w} (toRingCat J Osharp)}
  {gen : SheafOfModules.free (R := toRingCat J Osharp) ι ⟶ A.piece 1}

/-- **Contraction `δⱼ` by the `j`-th coordinate functional of the free sheaf of modules on a
finite index type, on an arbitrary exterior algebra of it**, from the homogeneous piece of degree
`p` to the one of degree `q`, for degrees with `q + 1 = p`. It is the transported Koszul
differential of Stacks tag 062K at the `j`-th coordinate functional, so it satisfies every law
proved there. -/
def coordKoszulD (hA : IsExteriorAlgebra A gen) (j : ι) {p q : ℤ} (h : q + 1 = p) :
    A.piece p ⟶ A.piece q :=
  hA.koszulD (Stacks.SheafOfModules.coordExteriorFunctional j) h

/-- The coordinate contraction is the transported Koszul differential at the `j`-th coordinate
functional. -/
theorem coordKoszulD_eq_koszulD (hA : IsExteriorAlgebra A gen) (j : ι) {p q : ℤ}
    (h : q + 1 = p) :
    hA.coordKoszulD j h = hA.koszulD (Stacks.SheafOfModules.coordExteriorFunctional j) h :=
  rfl

/-- **Contraction by two coordinate functionals anticommutes:** `δⱼ δₖ = - δₖ δⱼ`. For `k = j` the
two sides are equal to each other and the identity is vacuous; the vanishing of `δⱼ δⱼ` is
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.coordKoszulD_comp_coordKoszulD_self`. -/
theorem coordKoszulD_comp_coordKoszulD_comm (hA : IsExteriorAlgebra A gen) (j k : ι) {p q r : ℤ}
    (h : q + 1 = p) (h' : r + 1 = q) :
    hA.coordKoszulD k h ≫ hA.coordKoszulD j h' =
      -(hA.coordKoszulD j h ≫ hA.coordKoszulD k h') :=
  hA.koszulD_comp_koszulD_comm _ _ h h'

/-- **The square of a single coordinate contraction is zero.** This is the squaring law of the
transported Koszul differential, not a consequence of the anticommutation identity. -/
theorem coordKoszulD_comp_coordKoszulD_self (hA : IsExteriorAlgebra A gen) (j : ι) {p q r : ℤ}
    (h : q + 1 = p) (h' : r + 1 = q) :
    hA.coordKoszulD j h ≫ hA.coordKoszulD j h' = 0 :=
  hA.koszulD_comp_koszulD _ h h'

/-- **The coordinate contraction `δⱼ` anticommutes with the transported Koszul differential of an
arbitrary functional `φ`**, applied first. Taking `φ` to be the functional whose Koszul complex is
under study, this is one half of the identity `δⱼ d + d δⱼ = 0`. -/
theorem coordKoszulD_comp_koszulD_comm (hA : IsExteriorAlgebra A gen) (j : ι)
    (φ : PresheafOfModules.ExteriorFunctional.{v, u, w, w}
      (SheafOfModules.free (R := toRingCat J Osharp) ι).val)
    {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    hA.koszulD φ h ≫ hA.coordKoszulD j h' = -(hA.coordKoszulD j h ≫ hA.koszulD φ h') :=
  hA.koszulD_comp_koszulD_comm _ _ h h'

/-- **The coordinate contraction `δⱼ` anticommutes with the transported Koszul differential of an
arbitrary functional `φ`**, applied second. This is the other half of `δⱼ d + d δⱼ = 0`. -/
theorem koszulD_comp_coordKoszulD_comm (hA : IsExteriorAlgebra A gen) (j : ι)
    (φ : PresheafOfModules.ExteriorFunctional.{v, u, w, w}
      (SheafOfModules.free (R := toRingCat J Osharp) ι).val)
    {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    hA.coordKoszulD j h ≫ hA.koszulD φ h' = -(hA.koszulD φ h ≫ hA.coordKoszulD j h') :=
  hA.koszulD_comp_koszulD_comm _ _ h h'

end Coordinates

end SheafOfModules.GradedAlgebra.IsExteriorAlgebra

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

/-! ### The contractions on the exterior powers of a bundle of algebras -/

section Bundle

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F : SheafOfModules.{w} (toRingCat J Osharp)} (A : TensorExteriorSymmetricAlgebras J F)

/-- **The Koszul differential of a functional `φ` on the exterior powers of a bundle of tensor,
exterior and symmetric algebras of `F`.** The bundle's exterior algebra has the universal
property by its field `exterior_isExteriorAlgebra`, so this is the transported Koszul differential
at that field. -/
def koszulD (φ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val) {p q : ℤ}
    (h : q + 1 = p) : A.exterior.piece p ⟶ A.exterior.piece q :=
  A.exterior_isExteriorAlgebra.koszulD φ h

/-- **The Koszul differential of a functional on the exterior powers of a bundle squares to
zero.** -/
theorem koszulD_comp_koszulD (φ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val)
    {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) : A.koszulD φ h ≫ A.koszulD φ h' = 0 :=
  A.exterior_isExteriorAlgebra.koszulD_comp_koszulD φ h h'

/-- **The Koszul differentials of two functionals on the exterior powers of a bundle
anticommute.** -/
theorem koszulD_comp_koszulD_comm
    (φ ψ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val) {p q r : ℤ} (h : q + 1 = p)
    (h' : r + 1 = q) : A.koszulD ψ h ≫ A.koszulD φ h' = -(A.koszulD φ h ≫ A.koszulD ψ h') :=
  A.exterior_isExteriorAlgebra.koszulD_comp_koszulD_comm φ ψ h h'

end Bundle

section BundleCoordinates

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {ι : Type w} [DecidableEq ι] [Finite ι]
  (A : TensorExteriorSymmetricAlgebras J (SheafOfModules.free (R := toRingCat J Osharp) ι))

/-- **Contraction `δⱼ` by the `j`-th coordinate functional, on the exterior powers of a bundle of
algebras of the free sheaf of modules on a finite index type.** -/
def coordKoszulD (j : ι) {p q : ℤ} (h : q + 1 = p) :
    A.exterior.piece p ⟶ A.exterior.piece q :=
  A.exterior_isExteriorAlgebra.coordKoszulD j h

/-- The coordinate contraction on the exterior powers of a bundle is its Koszul differential at
the `j`-th coordinate functional. -/
theorem coordKoszulD_eq_koszulD (j : ι) {p q : ℤ} (h : q + 1 = p) :
    A.coordKoszulD j h = A.koszulD (Stacks.SheafOfModules.coordExteriorFunctional j) h :=
  rfl

/-- **Contraction by two coordinate functionals anticommutes** on the exterior powers of a
bundle: `δⱼ δₖ = - δₖ δⱼ`. -/
theorem coordKoszulD_comp_coordKoszulD_comm (j k : ι) {p q r : ℤ} (h : q + 1 = p)
    (h' : r + 1 = q) :
    A.coordKoszulD k h ≫ A.coordKoszulD j h' = -(A.coordKoszulD j h ≫ A.coordKoszulD k h') :=
  A.exterior_isExteriorAlgebra.coordKoszulD_comp_coordKoszulD_comm j k h h'

/-- **The square of a single coordinate contraction is zero** on the exterior powers of a
bundle. -/
theorem coordKoszulD_comp_coordKoszulD_self (j : ι) {p q r : ℤ} (h : q + 1 = p)
    (h' : r + 1 = q) : A.coordKoszulD j h ≫ A.coordKoszulD j h' = 0 :=
  A.exterior_isExteriorAlgebra.coordKoszulD_comp_coordKoszulD_self j h h'

/-- **`δⱼ` anticommutes with the Koszul differential of an arbitrary functional `φ`** on the
exterior powers of a bundle, applied first. -/
theorem coordKoszulD_comp_koszulD_comm (j : ι)
    (φ : PresheafOfModules.ExteriorFunctional.{v, u, w, w}
      (SheafOfModules.free (R := toRingCat J Osharp) ι).val)
    {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    A.koszulD φ h ≫ A.coordKoszulD j h' = -(A.coordKoszulD j h ≫ A.koszulD φ h') :=
  A.exterior_isExteriorAlgebra.coordKoszulD_comp_koszulD_comm j φ h h'

/-- **`δⱼ` anticommutes with the Koszul differential of an arbitrary functional `φ`** on the
exterior powers of a bundle, applied second. -/
theorem koszulD_comp_coordKoszulD_comm (j : ι)
    (φ : PresheafOfModules.ExteriorFunctional.{v, u, w, w}
      (SheafOfModules.free (R := toRingCat J Osharp) ι).val)
    {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    A.coordKoszulD j h ≫ A.koszulD φ h' = -(A.koszulD φ h ≫ A.coordKoszulD j h') :=
  A.exterior_isExteriorAlgebra.koszulD_comp_coordKoszulD_comm j φ h h'

end BundleCoordinates

end SheafOfModules.TensorExteriorSymmetricAlgebras

namespace Stacks.RegularSequence.KoszulChainData

/-! ### The contractions on the terms of the Koszul chain complex -/

section Chain

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F : SheafOfModules.{w} (toRingCat J Osharp)}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras J F}
  {g : F ⟶ SheafOfModules.unit (toRingCat J Osharp)} (K : KoszulChainData A g)

/-- **The degree-`n` term of the Koszul chain complex is the degree-`n` exterior power**, read as
an isomorphism rather than as the equality of objects `chain_X`. -/
def chainXIso (n : ℤ) : A.exterior.piece n ≅ K.chain.X n :=
  eqToIso (K.chain_X n).symm

/-- **The Koszul differential of a functional `φ` on the terms of the Koszul chain complex.** It
is the differential on the exterior powers, read through the identification of a term of the
complex with an exterior power. -/
def koszulD (φ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val) {p q : ℤ}
    (h : q + 1 = p) : K.chain.X p ⟶ K.chain.X q :=
  (K.chainXIso p).inv ≫ A.koszulD φ h ≫ (K.chainXIso q).hom

/-- **The Koszul differential of a functional on the terms of the Koszul chain complex squares to
zero.** -/
theorem koszulD_comp_koszulD (φ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val)
    {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) : K.koszulD φ h ≫ K.koszulD φ h' = 0 := by
  exact iso_conj_comp_eq_zero _ _ _ (A.koszulD_comp_koszulD φ h h')

/-- **The Koszul differentials of two functionals on the terms of the Koszul chain complex
anticommute.** -/
theorem koszulD_comp_koszulD_comm
    (φ ψ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val) {p q r : ℤ} (h : q + 1 = p)
    (h' : r + 1 = q) : K.koszulD ψ h ≫ K.koszulD φ h' = -(K.koszulD φ h ≫ K.koszulD ψ h') := by
  exact iso_conj_comp_comm _ _ _ (A.koszulD_comp_koszulD_comm φ ψ h h')

end Chain

section ChainCoordinates

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {ι : Type w} [DecidableEq ι] [Finite ι]
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras J
    (SheafOfModules.free (R := toRingCat J Osharp) ι)}
  {g : SheafOfModules.free (R := toRingCat J Osharp) ι ⟶
    SheafOfModules.unit (toRingCat J Osharp)} (K : KoszulChainData A g)

/-- **Contraction `δⱼ` by the `j`-th coordinate functional, on the terms of the Koszul chain
complex of a functional on the free sheaf of modules on a finite index type.** A consumer of this
operator never mentions the comparison with the realized exterior algebra, nor the equality of
objects identifying a term of the complex with an exterior power. -/
def coordKoszulD (j : ι) {p q : ℤ} (h : q + 1 = p) : K.chain.X p ⟶ K.chain.X q :=
  (K.chainXIso p).inv ≫ A.coordKoszulD j h ≫ (K.chainXIso q).hom

/-- The coordinate contraction on the terms of the Koszul chain complex is its Koszul differential
at the `j`-th coordinate functional. -/
theorem coordKoszulD_eq_koszulD (j : ι) {p q : ℤ} (h : q + 1 = p) :
    K.coordKoszulD j h = K.koszulD (Stacks.SheafOfModules.coordExteriorFunctional j) h :=
  rfl

/-- **Contraction by two coordinate functionals anticommutes** on the terms of the Koszul chain
complex: `δⱼ δₖ = - δₖ δⱼ`. -/
theorem coordKoszulD_comp_coordKoszulD_comm (j k : ι) {p q r : ℤ} (h : q + 1 = p)
    (h' : r + 1 = q) :
    K.coordKoszulD k h ≫ K.coordKoszulD j h' = -(K.coordKoszulD j h ≫ K.coordKoszulD k h') :=
  K.koszulD_comp_koszulD_comm _ _ h h'

/-- **The square of a single coordinate contraction is zero** on the terms of the Koszul chain
complex. -/
theorem coordKoszulD_comp_coordKoszulD_self (j : ι) {p q r : ℤ} (h : q + 1 = p)
    (h' : r + 1 = q) : K.coordKoszulD j h ≫ K.coordKoszulD j h' = 0 :=
  K.koszulD_comp_koszulD _ h h'

/-- **`δⱼ` anticommutes with the Koszul differential of an arbitrary functional `φ`** on the terms
of the Koszul chain complex, applied first. This is one half of `δⱼ d_φ + d_φ δⱼ = 0`. -/
theorem coordKoszulD_comp_koszulD_comm (j : ι)
    (φ : PresheafOfModules.ExteriorFunctional.{v, u, w, w}
      (SheafOfModules.free (R := toRingCat J Osharp) ι).val)
    {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    K.koszulD φ h ≫ K.coordKoszulD j h' = -(K.coordKoszulD j h ≫ K.koszulD φ h') :=
  K.koszulD_comp_koszulD_comm _ _ h h'

/-- **`δⱼ` anticommutes with the Koszul differential of an arbitrary functional `φ`** on the terms
of the Koszul chain complex, applied second. This is the other half of
`δⱼ d_φ + d_φ δⱼ = 0`. -/
theorem koszulD_comp_coordKoszulD_comm (j : ι)
    (φ : PresheafOfModules.ExteriorFunctional.{v, u, w, w}
      (SheafOfModules.free (R := toRingCat J Osharp) ι).val)
    {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    K.coordKoszulD j h ≫ K.koszulD φ h' = -(K.koszulD φ h ≫ K.coordKoszulD j h') :=
  K.koszulD_comp_koszulD_comm _ _ h h'

end ChainCoordinates

end Stacks.RegularSequence.KoszulChainData

end
