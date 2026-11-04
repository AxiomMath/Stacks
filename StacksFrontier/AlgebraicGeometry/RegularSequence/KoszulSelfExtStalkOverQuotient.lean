module

public import StacksFrontier.Algebra.Module.LinearityOverASurjection
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtStructureStalkDual
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulIteratedContractionClass
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtAlgebraDescent
public import StacksFrontier.Topology.Sheaves.Modules.ConormalSheafStalk

/-!
# The self-Ext algebra at a stalk, linearly over the stalk of the quotient

Let `O♯` be a sheaf of commutative rings on a space, let `φ : (O♯)ʳ ⟶ O♯` generate a sheaf of
ideals, write `O_X = O♯/𝓘`, and let `K` be a Koszul complex resolving the quotient. The self-Ext
sheaves carry a graded `O♯`-algebra structure under composition and descend to a graded
`O_X`-algebra `Stacks.RegularSequence.KoszulChainData.extSelfAlgebra`. This file identifies the
stalk of its degree-`m` piece **linearly over the stalk `(O_X)_x`**:

`((extSelfAlgebra).piece m)_x  ≃ₗ[(O_X)_x]  Hom_{(O_X)_x}(⋀ᵐ_{(O_X)_x}(((O_X)_x)ʳ), (O_X)_x)`.

Every identification of this stalk available until now was linear over the stalk `O_x` of `O♯`
only — `Stacks.RegularSequence.KoszulChainData.extStalkEquiv` is, and
`Stacks.RegularSequence.KoszulChainData.extStructureStalkDualEquiv` is in consequence a bijection
of types rather than a linear equivalence. That is what this file repairs, and it is what makes
the recognition route `Koszul.bijective_of_listContractionDual` applicable: that theorem consumes
a map linear over the ring of the exterior power, and the exterior power in question is formed
over `(O_X)_x`.

## Main definitions

* `Stacks.RegularSequence.KoszulChainData.descendSectionAddEquiv` and
  `Stacks.RegularSequence.KoszulChainData.descendStalkAddEquiv`: the sections, respectively the
  stalk, of a piece of the descended algebra, identified with those of the original piece.
* `Stacks.RegularSequence.KoszulChainData.homologyPieceIsoExt`: the piece of the self-Ext algebra
  before descent, identified with the Ext sheaf.
* `Stacks.RegularSequence.KoszulChainData.homologyPieceStalkEquiv` and
  `Stacks.RegularSequence.KoszulChainData.homologyPieceStalkStructureEquiv`: its stalk as
  `O_x`-linear maps out of an exterior power, which is `extStalkEquiv` transported, and the same
  with the coefficients read as the stalk of `O_X`.
* `Stacks.RegularSequence.KoszulChainData.quotientStalkHom`: the stalk of the quotient map, with
  its codomain spelled so that its values act on stalks of sheaves of `O_X`-modules.
* `Stacks.RegularSequence.KoszulChainData.extSelfAlgebraStalkDualEquiv`: **the identification
  displayed above**, an honest `(O_X)_x`-linear equivalence.

## Main results

* `Stacks.RegularSequence.KoszulChainData.descendSectionAddEquiv_smul` and
  `Stacks.RegularSequence.KoszulChainData.descendStalkAddEquiv_smul`: **the identification is
  semilinear**, carrying the action of a scalar of `O♯` to the action of its image in `O_X`.
* `Stacks.RegularSequence.KoszulChainData.descendPieceAddEquiv_homogeneousProd`: **the ordered
  product of degree-one local sections is unchanged by descent**, which is what joins the cocycle
  half of the local computation to the comparison map of the tag.
* `Stacks.RegularSequence.KoszulChainData.surjective_quotientStalkRingHom`: the stalk of the
  quotient map is surjective.

## Implementation notes

**Descent leaves the underlying presheaf of abelian groups untouched, so the two stalks are the
same type.** `SheafOfModules.GradedAlgebra.descend` takes the piece to
`Stacks.SheafOfModules.ChangeOfRings.liftedSheaf`, whose underlying presheaf is literally the
original one by `PresheafOfModules.ofPresheaf_presheaf`. The identifications here are therefore
`AddEquiv.refl`, and all the content is in the `_smul` lemmas.

**They cannot be stated as linear or semilinear maps, and that is why `AddEquiv` appears.** The
`O_x`-action is an instance at the spelling of the original piece and the `(O_X)_x`-action at the
spelling of the descended one; neither action is an instance at the other spelling, so a single
`•` cannot be written for both and instance search fails on any attempt to mix them. Writing the
identity as a *bundled* `AddEquiv` between the two spellings pins each `•` to its own side, which
is what makes the statements elaborate at all. An ascription `(s : other spelling)` does not
work: it is not a coercion, so instance search still sees the original type.

**The upgrade to `(O_X)_x`-linearity is `Stacks.Module.LinearEquiv.ofSemilinearAddEquiv`**, and it
needs the stalk of the quotient map to be surjective — which it is, local surjectivity having been
spent in passing to the stalk. Mathlib's `LinearMap.extendScalarsOfSurjective` does not apply, for
the reason in the previous note: it asks for both actions as instances on one module.

**The target of the `O_x`-linear identification already carries both actions.** It is a module of
`O_x`-linear maps into `(O_X)_x`, on which a scalar of `(O_X)_x` acts through the target; the two
actions are compatible and `IsScalarTower` is found by instance search, so it is an admissible
target for the upgrade without any new structure.

**What is still missing, and where it would go.** The identification here is not yet matched with
the stalk of the comparison map, so the tag does not follow. What remains is one chain, of which
every link but the first has its ingredients in place. First, the value of
`Stacks.RegularSequence.KoszulChainData.homIso` on the class of the iterated-contraction cocycle,
as an explicit local homomorphism out of an exterior power: `homIso_hom` reduces this to the
degree-`n` component of a pushforward, and
`AlgebraicGeometry.RingedSite.applyHomSectionOver_homMap` together with
`Stacks.RegularSequence.KoszulChainData.applyHomSectionOver_iteratedContractionSection` compute
that component, but the degree transports relating the two spellings of the intermediate degree
have to be discharged. Then that homomorphism, paired against a basis wedge at a stalk, is the
iterated contraction, which is
`SheafOfModules.TensorExteriorSymmetricAlgebras.listContractionDual_exteriorKoszulStalkEquiv` —
stated over `O_x`, so it must be carried across `exteriorPower.homFreeBaseChangeEquiv` to the
stalk of `O_X`. Finally `Koszul.bijective_of_listContractionDual` asks for the contraction formula
at *every* family of functionals on the free module, not only at the coordinate projections; both
sides are alternating and multilinear in the family, so a basis suffices, but that multilinearity
is not recorded anywhere and is the one genuinely new ingredient.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex Stacks.ChainComplex

universe u

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.Sites Stacks.SheafOfModules Stacks.SheafOfModules.SheafHomStalk Stacks.RegularSequence

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}
  (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation]

/-! ### The sections and the stalk of a descended piece -/

/-- **The sections of a piece of the descended self-Ext algebra are the sections of the piece
before descent.** Descent along the quotient of the ring sheaf leaves the underlying presheaf of
abelian groups untouched, so this is the identity; it is bundled as an additive equivalence so
that each of the two scalar actions can be written on its own side. -/
def descendSectionAddEquiv (n : ℤ) (U : (Opens ↥X)ᵒᵖ) :
    (commVal (Rc := Rc) ((homologyGradedAlgebra Rc (cochain Rc K)).piece n)).obj U ≃+
      (commVal (Rc := quotientStructureSheaf Rc φ) ((extSelfAlgebra Rc K).piece n)).obj U :=
  AddEquiv.refl _

/-- **The identification of sections is semilinear**: it carries the action of a section `a` of
`O♯` to the action of the image of `a` in `O_X`. This is the defining property of the lifted
action, `Stacks.SheafOfModules.ChangeOfRings.liftedSMul_app`: the lifted action of the image of a
scalar is the original action of that scalar.

The scalar on the right names the spelling `quotientStructureSheaf Rc φ` of the quotient sheaf of
rings, which is the one the module structure on sections of the descended piece is indexed by:
`Stacks.Sites.toQuotientRingSheaf` lands in `Stacks.Sites.quotientRingSheaf` of the sheaf of
ideals, and the two are the same sheaf of rings by `rfl`, but `quotientStructureSheaf` is a plain
definition, so instance search does not identify them and the action on sections is not found at
the unpinned spelling. -/
theorem descendSectionAddEquiv_smul (n : ℤ) (U : (Opens ↥X)ᵒᵖ) (a : Rc.obj.obj U)
    (s : (commVal (Rc := Rc) ((homologyGradedAlgebra Rc (cochain Rc K)).piece n)).obj U) :
    descendSectionAddEquiv Rc K n U (a • s) =
      (show (quotientStructureSheaf Rc φ).obj.obj U from
          (toQuotientRingSheaf.{u, u, u} (quotientIdeal Rc φ)).hom.app U a) •
        descendSectionAddEquiv Rc K n U s := by
  have : Sheaf.IsLocallySurjective (quotientRingHom (quotientIdeal Rc φ)) :=
    isLocallySurjective_quotientRingHom_idealOfHom φ
  exact (Stacks.SheafOfModules.ChangeOfRings.liftedSMul_app
    (quotientRingHom (quotientIdeal Rc φ))
    ((homologyGradedAlgebra Rc (cochain Rc K)).piece n)
    (smul_homologyPiece_eq_zero Rc K n) a s).symm

/-- **The stalk of a piece of the descended self-Ext algebra is the stalk of the piece before
descent.** As for sections, this is the identity, bundled so that the two actions of scalars —
of `O_x` on the one side, of `(O_X)_x` on the other — can each be written. -/
def descendStalkAddEquiv (n : ℤ) (x : ↥X) :
    modStalk (Rc := Rc) ((homologyGradedAlgebra Rc (cochain Rc K)).piece n) x ≃+
      modStalk (Rc := quotientStructureSheaf Rc φ) ((extSelfAlgebra Rc K).piece n) x :=
  AddEquiv.refl _

omit [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The stalk of the quotient map is surjective.** A locally surjective morphism of presheaves
of commutative rings is surjective on stalks, and the quotient map onto a quotient by a sheaf of
ideals is locally surjective. -/
theorem surjective_quotientStalkRingHom (x : ↥X) :
    Function.Surjective (quotientStalkRingHom Rc φ x).hom := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X)
      (toQuotientRingSheaf.{u, u, u} (quotientIdeal Rc φ)).hom :=
    Stacks.Sites.isLocallySurjective_toQuotientRingSheaf (quotientIdeal Rc φ)
  exact Stacks.Sites.Conormal.stalkMap_surjective
    (toQuotientRingSheaf.{u, u, u} (quotientIdeal Rc φ)).hom x

omit [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The stalk of the quotient map, with its codomain spelled as the stalk of the quotient sheaf
of rings.** `Stacks.RegularSequence.quotientStalkRingHom` is built as the image of the quotient map
under the stalk functor, so its codomain reads as a functor application; the module structures on
stalks are stated at `TopCat.Presheaf.stalk`. The two are definitionally equal but not
syntactically so, and instance search for the scalar action fails at the former. A definition with
the result type ascribed pins the spelling, which is what lets a scalar of the stalk of `O_X` act
on the stalk of a sheaf of `O_X`-modules at all. -/
def quotientStalkHom (x : ↥X) :
    ↑(ringStalk Rc x) →+* ↑(quotientStructureStalk Rc φ x) :=
  (quotientStalkRingHom Rc φ x).hom

omit [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The algebra structure on the stalk of `O_X` over the stalk of `O♯` is the one given by
`quotientStalkHom`. -/
theorem algebraMap_quotientStalkAlgebra (x : ↥X) :
    letI := quotientStalkAlgebra Rc φ x
    algebraMap ↑(ringStalk Rc x) ↑(quotientStructureStalk Rc φ x) =
      quotientStalkHom Rc (φ := φ) x :=
  rfl

omit [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Germwise description of `quotientStalkHom`: the image of the germ of a section is the germ of
its image. -/
theorem quotientStalkHom_germ (x : ↥X) (W : Opens ↥X) (hx : x ∈ W) (a : Rc.obj.obj (op W)) :
    quotientStalkHom Rc (φ := φ) x (TopCat.Presheaf.germ Rc.obj W x hx a) =
      TopCat.Presheaf.germ (quotientStructureSheaf Rc φ).obj W x hx
        ((toQuotientRingSheaf.{u, u, u} (quotientIdeal Rc φ)).hom.app (op W) a) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply W x hx
    (toQuotientRingSheaf.{u, u, u} (quotientIdeal Rc φ)).hom a

omit [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The stalk of the quotient map is surjective**, in the spelling of `quotientStalkHom`. -/
theorem surjective_quotientStalkHom (x : ↥X) :
    Function.Surjective (quotientStalkHom Rc (φ := φ) x) :=
  surjective_quotientStalkRingHom Rc (φ := φ) x

/-- The stalk identification on germs: it is the identity, so it carries the germ of a section to
the germ of the same section read on the descended piece. -/
theorem descendStalkAddEquiv_germAt (n : ℤ) (x : ↥X) (W : Opens ↥X) (hx : x ∈ W)
    (t : (commVal (Rc := Rc) ((homologyGradedAlgebra Rc (cochain Rc K)).piece n)).obj (op W)) :
    descendStalkAddEquiv Rc K n x
        (germAt ((homologyGradedAlgebra Rc (cochain Rc K)).piece n) W x hx t) =
      germAt (Rc := quotientStructureSheaf Rc φ) ((extSelfAlgebra Rc K).piece n) W x hx
        (descendSectionAddEquiv Rc K n (op W) t) := rfl

/-- **The stalk identification is semilinear**: it carries the action of a germ `a` of `O♯` to the
action of the image of `a` in the stalk of `O_X`.

Proved on germs. A germ of `O♯` and a germ of the piece are brought onto a common open, the scalar
is moved inside the germ by `germAt_smul`, the identification of germs is the identity, and the
image of the germ of the scalar is the germ of its image by
`TopCat.Presheaf.stalkFunctor_map_germ_apply`; what is left is the section-level statement
`descendSectionAddEquiv_smul`. -/
theorem descendStalkAddEquiv_smul (n : ℤ) (x : ↥X) (a : ↑(ringStalk Rc x))
    (m : modStalk (Rc := Rc) ((homologyGradedAlgebra Rc (cochain Rc K)).piece n) x) :
    descendStalkAddEquiv Rc K n x (a • m) =
      quotientStalkHom Rc (φ := φ) x a • descendStalkAddEquiv Rc K n x m := by
  obtain ⟨U₁, hU₁, a₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq (X := X) Rc.obj a
  obtain ⟨U₂, hU₂, s, rfl⟩ :=
    exists_germ_eq ((homologyGradedAlgebra Rc (cochain Rc K)).piece n) m
  have hmem : x ∈ U₁ ⊓ U₂ := mem_inf hU₁ hU₂
  rw [← TopCat.Presheaf.germ_res_apply (X := X) Rc.obj
      (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) x hmem a₀,
    ← germAt_resLE ((homologyGradedAlgebra Rc (cochain Rc K)).piece n)
      (inf_le_right : U₁ ⊓ U₂ ≤ U₂) hmem s,
    ← germAt_smul ((homologyGradedAlgebra Rc (cochain Rc K)).piece n) hmem _ _,
    descendStalkAddEquiv_germAt, descendStalkAddEquiv_germAt, descendSectionAddEquiv_smul,
    quotientStalkHom_germ Rc (φ := φ) x (U₁ ⊓ U₂) hmem]
  exact germAt_smul (Rc := quotientStructureSheaf Rc φ) ((extSelfAlgebra Rc K).piece n) hmem _ _

/-! ### The ordered product of degree-one sections survives descent -/

/-- **The sections of a piece of the descended algebra are the sections of the original piece**, in
the spelling `(piece n).val.obj U` that the graded multiplication uses. As
`descendSectionAddEquiv`, this is the identity bundled so that each side keeps its own scalars. -/
def descendPieceAddEquiv (n : ℤ) (U : (Opens ↥X)ᵒᵖ) :
    ((homologyGradedAlgebra Rc (cochain Rc K)).piece n).val.obj U ≃+
      ((extSelfAlgebra Rc K).piece n).val.obj U :=
  AddEquiv.refl _

/-- **The ordered product of degree-one local sections is unchanged by descent.** The descended
algebra has the same multiplication and the same unit on sections as the original —
`SheafOfModules.GradedAlgebra.descend_mul_app` and
`SheafOfModules.GradedAlgebra.descend_one_eval` are both `rfl` — so the two ordered products
agree, by the induction that defines them.

This is what joins the two halves of the local computation. The cocycle half,
`Stacks.RegularSequence.KoszulChainData.homogeneousProd_contractionClassOn`, is stated for the
ordered product of the algebra **before** descent; the comparison map of the tag,
`Stacks.RegularSequence.KoszulChainData.extComparison_app_homogeneousProd`, is stated for the
ordered product **after** descent. The two cannot be identified by unfolding: the pieces are
modules over different rings, so the statement does not even typecheck without transporting one
side, and for a variable number of factors it is not a definitional equality either. -/
theorem descendPieceAddEquiv_homogeneousProd (n : ℕ) (U : (Opens ↥X)ᵒᵖ)
    (z : Fin n → ((homologyGradedAlgebra Rc (cochain Rc K)).piece 1).val.obj U) :
    descendPieceAddEquiv Rc K (n : ℤ) U
        ((homologyGradedAlgebra Rc (cochain Rc K)).toPresheafGradedAlgebra.homogeneousProd
          U n z) =
      (extSelfAlgebra Rc K).toPresheafGradedAlgebra.homogeneousProd U n
        (fun i => descendPieceAddEquiv Rc K 1 U (z i)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [homogeneousProd_succ_right
          (homologyGradedAlgebra Rc (cochain Rc K)).toPresheafGradedAlgebra U k,
        homogeneousProd_succ_right (extSelfAlgebra Rc K).toPresheafGradedAlgebra U k,
        ← ih (fun i => z i.castSucc)]
      rfl

/-! ### The stalk of a piece, linearly over the stalk of the quotient -/

/-- **The piece of the self-Ext algebra before descent, identified with the Ext sheaf.** These are
the first two factors of `Stacks.RegularSequence.KoszulChainData.homIso`: the cochain-level
identification of the Ext sheaf with the cohomology of the internal endomorphism complex,
inverted, followed by the transport of the target along the augmentation. -/
def homologyPieceIsoExt (n : ℤ) :
    (homologyGradedAlgebra Rc (cochain Rc K)).piece n ≅
      derivedSheafExt Rc
        (DerivedCategory.Q.obj
          ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
            (quotient Rc (φ := φ))))
        (DerivedCategory.Q.obj
          ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
            (quotient Rc (φ := φ)))) n :=
  (derivedSheafExtIsoHomologyCochain Rc K (cochain Rc K) n).symm ≪≫
    derivedSheafExtMapIso Rc n (Iso.refl _)
      (asIso (DerivedCategory.Q.map (cochainAugmentation Rc K)) ≪≫
        DerivedCategory.Q.mapIso (quotientSingleIso Rc (φ := φ)))

omit [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}] in
/-- **`homIso` factors through `homologyPieceIsoExt`.** The identification of a piece of the
self-Ext algebra with an internal Hom sheaf is the identification with the Ext sheaf followed by
the computation of the Ext sheaf, which is how the formula of
`Stacks.RegularSequence.KoszulChainData.homIso_hom` meets the stalk description below: the first
factor of `homologyPieceStalkEquiv` is the first factor of `homIso`, and the remaining factors of
`extStalkEquiv` begin with the second. -/
theorem homIso_eq (n : ℤ) :
    homIso Rc K n = homologyPieceIsoExt Rc K n ≪≫ extIsoInternalHom Rc K n :=
  (Iso.trans_assoc _ _ _).symm

/-- **The stalk of a piece of the self-Ext algebra before descent, as `O_x`-linear maps out of an
exterior power.** This is `Stacks.RegularSequence.KoszulChainData.extStalkEquiv` transported along
`homologyPieceIsoExt`; like it, it is linear over the stalk of `O♯` only. -/
def homologyPieceStalkEquiv (m : ℕ) (x : ↥X) :
    modStalk (Rc := Rc) ((homologyGradedAlgebra Rc (cochain Rc K)).piece ((m : ℕ) : ℤ)) x ≃ₗ[
        ringStalk Rc x]
      (⋀[↑(TopCat.Presheaf.stalk Rc.obj x)]^m (Fin r → ↑(TopCat.Presheaf.stalk Rc.obj x)) →ₗ[
        ringStalk Rc x] modStalk (quotient Rc (φ := φ)) x) :=
  modStalkEquivOfIso Rc (homologyPieceIsoExt Rc K ((m : ℕ) : ℤ)) x ≪≫ₗ extStalkEquiv Rc K m x

/-- **The stalk of a piece of the self-Ext algebra, as `O_x`-linear maps into the stalk of
`O_X`.** The coefficient module of `homologyPieceStalkEquiv` is replaced by the stalk of the
quotient sheaf of rings, which is the `O_x`-linear identification
`Stacks.RegularSequence.cokernelStalkLinearEquivStructureStalk`. The target is a module of
`O_x`-linear maps into an `O_x`-algebra, so it carries an action of that algebra as well, and the
two are compatible — which is what makes it an admissible target for the upgrade below. -/
def homologyPieceStalkStructureEquiv (m : ℕ) (x : ↥X) :=
  letI := quotientStalkAlgebra Rc φ x
  (homologyPieceStalkEquiv Rc K m x ≪≫ₗ
    LinearEquiv.arrowCongr (LinearEquiv.refl (ringStalk Rc x) _)
      (cokernelStalkLinearEquivStructureStalk Rc φ x) :
    modStalk (Rc := Rc) ((homologyGradedAlgebra Rc (cochain Rc K)).piece ((m : ℕ) : ℤ)) x ≃ₗ[
        ringStalk Rc x]
      (⋀[↑(TopCat.Presheaf.stalk Rc.obj x)]^m (Fin r → ↑(TopCat.Presheaf.stalk Rc.obj x)) →ₗ[
        ringStalk Rc x] ↑(quotientStructureStalk Rc φ x)))

/-- **The stalk of a piece of the self-Ext algebra is the dual of an exterior power of a free
module, linearly over the stalk of `O_X`.** At a point `x`, writing `S` for the stalk of `O_X`,

`((extSelfAlgebra).piece m)_x  ≃ₗ[S]  Hom_S(⋀ᵐ_S(Sʳ), S)`.

This is the statement that
`Stacks.RegularSequence.KoszulChainData.extStructureStalkDualEquiv` makes only as a bijection of
types, now **linear over `S`** — which is what the recognition route
`Koszul.bijective_of_listContractionDual` consumes, that theorem asking for a map linear over the
ring of the exterior power.

Two things make the upgrade possible. The stalk of the descended piece is the stalk of the piece
before descent, semilinearly over the quotient map
(`descendStalkAddEquiv`, `descendStalkAddEquiv_smul`), so an identification proved over `O_x` can
be read on it; and the stalk of the quotient map is surjective
(`surjective_quotientStalkHom`), so semilinearity plus `O_x`-linearity give `S`-linearity, by
`Stacks.Module.LinearEquiv.ofSemilinearAddEquiv`. The final factor
`exteriorPower.homFreeBaseChangeEquiv` is already `S`-linear and turns `O_x`-linear maps into `S`
into `S`-linear functionals on the exterior power formed over `S`. -/
def extSelfAlgebraStalkDualEquiv (m : ℕ) (x : ↥X) :=
  letI := quotientStalkAlgebra Rc φ x
  (Stacks.Module.LinearEquiv.ofSemilinearAddEquiv (surjective_quotientStalkHom Rc (φ := φ) x)
      (descendStalkAddEquiv Rc K ((m : ℕ) : ℤ) x)
      (descendStalkAddEquiv_smul Rc K ((m : ℕ) : ℤ) x)
      (homologyPieceStalkStructureEquiv Rc K m x) ≪≫ₗ
    exteriorPower.homFreeBaseChangeEquiv ↑(ringStalk Rc x)
      ↑(quotientStructureStalk Rc φ x) (Fin r) m :
    modStalk (Rc := quotientStructureSheaf Rc φ)
        ((extSelfAlgebra Rc K).piece ((m : ℕ) : ℤ)) x ≃ₗ[
        ↑(quotientStructureStalk Rc φ x)]
      Module.Dual ↑(quotientStructureStalk Rc φ x)
        (⋀[↑(quotientStructureStalk Rc φ x)]^m (Fin r → ↑(quotientStructureStalk Rc φ x))))

end Stacks.RegularSequence.KoszulChainData

end
