module

public import StacksFrontier.Algebra.Homology.HomologyOfZeroDifferentialsCycles
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtDegreeOneGenerated
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulIteratedContractionClass
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtAlgebraDescent
public import StacksFrontier.CategoryTheory.CommutingSquares
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomDegreeProjectionEvaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.ExtFromStrictlyPerfectResolutionNaturality

/-!
# The self-Ext identification is pushforward along the augmentation

Let `O♯` be a sheaf of commutative rings on a space, let `φ : (O♯)ʳ ⟶ O♯` generate a sheaf of
ideals, write `O_X = O♯/𝓘`, and let `K` be a Koszul complex resolving the quotient. The pieces of
the self-Ext algebra are the cohomology sheaves of the internal endomorphism complex
`SheafHom^•(K, K)`, and `Stacks.RegularSequence.KoszulChainData.homIso` identifies the degree-`n`
piece with the internal Hom sheaf `SheafHom_{O♯}(K_n, O_X)`.

That identification is built out of two derived-category comparisons and is opaque as it stands.
This file computes it: it is **pushforward along the augmentation**, followed by reading off the
degree-`n` term of a complex with vanishing differentials and projecting onto its single
nonvanishing component. In symbols,

`homIso n = H^n(SheafHom^•(K, α)) ≫ (H^n ≅ (-)^n) ≫ (proj at q = n)`,

where `α : K^• ⟶ O_X[0]` is the augmentation read into the cochain complex concentrated in degree
zero. So the identification carries the class of a degree-`n` cocycle of `SheafHom^•(K, K)` to the
homomorphism `K_n ⟶ O_X` obtained by taking that cocycle's component out of cochain degree `-n`
and composing it with the augmentation — which is the description the Stacks proof of Tag 0BQY
uses when it replaces `Hom^•(A, A)` by `Hom^•(A, O_X)`.

## Main results

* `Stacks.RegularSequence.KoszulChainData.derivedSheafExtIsoHomologyCochain_augmentation`: the
  two cochain-level identifications, at the endomorphism complex and at the complex concentrated
  in degree zero, are intertwined by pushforward along the augmentation.
* `Stacks.RegularSequence.KoszulChainData.homIso_hom`: **the formula above**, the degree-`n` piece
  of the self-Ext algebra identified with `SheafHom(K_n, O_X)` by pushforward along the
  augmentation.
* `Stacks.RegularSequence.KoszulChainData.homologyπ_comp_homIso_hom` and
  `Stacks.RegularSequence.KoszulChainData.homIso_hom_val_app_homologyπ`: **the identification
  evaluated on the class of a cocycle**, as a composite of morphisms and on local sections. The
  class of a degree-`n` cocycle goes to that cocycle's degree-`n` component composed with the
  augmentation; no cohomology class and no derived-category object remain on the right.
* `Stacks.RegularSequence.KoszulChainData.homIso_app_apply`: **the identification evaluated all the
  way down**, as the value of the resulting homomorphism on a section of `K_n` — the `(-n, n - n)`
  component of the cocycle applied to that section, then the augmentation.
* `AlgebraicGeometry.RingedSite.homDegreeIsoSingle_app_apply`: the degree projection onto a complex
  concentrated in degree zero, evaluated on a section.

## Implementation notes

**On a class, each of the three factors loses its cohomology class in turn.** The pushforward on
cohomology sheaves commutes with the projection onto cohomology; the identification of the
cohomology of a complex with vanishing differentials with its degree-`n` term carries the class of
a cycle to that cycle, which is
`Stacks.CochainComplex.homologyπ_comp_intHomologyIsoX_hom`, proved for this purpose; and the
inclusion of the cycles commutes with the pushforward. What is left is a composite of the
inclusion of the cycles, the pushforward in degree `n`, and a projection — all three of which have
section-level formulas already.

**The input is naturality in the target, and the three Ext maps between the two uses of it
collapse.** `Stacks.SheafOfModules.derivedSheafExtIsoHomologyOfResolution_naturality_target` is
stated for the resolution form of the identification, whose source is the object resolved by the
Koszul cochain complex — the complex concentrated in degree zero on the quotient, read as a
cochain complex. `Stacks.RegularSequence.KoszulChainData.derivedSheafExtIsoHomologyCochain`
reindexes that source onto the cochain complex concentrated in degree zero, by a transport in the
*first* variable. Between the inverse of the identification at the endomorphism complex and the
identification at the complex concentrated in degree zero there are therefore three maps of Ext
sheaves: that transport inverted, the pushforward along the augmentation, and that transport
again. They compose to the pushforward alone, the transport cancelling against its inverse by
`Stacks.SheafOfModules.derivedSheafExtMap_comp`; what is left is exactly an instance of the
naturality square.

**The augmentation is composed with the reindexing isomorphism before it is used.** The Koszul
cochain augmentation lands in the *reindexed* complex concentrated in degree zero, whereas the
second variable of the Ext sheaf in the self-Ext algebra is the cochain complex concentrated in
degree zero. `Stacks.RegularSequence.KoszulChainData.augSingle` is the augmentation followed by
the comparison of those two, and it is the morphism of complexes whose pushforward the formula
names — matching the second factor of
`Stacks.RegularSequence.KoszulChainData.homIso`, which is the image of that same composite under
the localisation functor.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex Stacks.ChainComplex

universe u

namespace AlgebraicGeometry.RingedSite

/-- **The isomorphism onto a complex concentrated in degree zero, evaluated on a section.** The
section that `AlgebraicGeometry.RingedSite.homDegreeIsoSingle` produces out of a degree-`n` section
of the internal Hom complex is the `(-n, n - n)` component of the corresponding cochain, with its
value transported along the identification of the degree `n - n` term of the complex concentrated
in degree zero with the module itself.

Stated here rather than with the other evaluation lemmas because `homDegreeIsoSingle` is defined
alongside the computation of the Ext sheaves of a Koszul-regular quotient, not with the general
internal Hom complex. -/
theorem homDegreeIsoSingle_app_apply (Y : RingedSite.{u, u, u})
    [CategoryTheory.HasSheafify Y.J AddCommGrpCat.{u}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (n : ℤ) (U V : Y.C) (i : V ⟶ U)
    (s : ((sheafHomComplex Y E
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ) 0).obj N)).obj.X n).val.obj (op U))
    (y : ((E.X (-n)).over U).val.obj (op (Over.mk i))) :
    ((homDegreeIsoSingle Y E N n).hom.val.app (op U) s).app (op (Over.mk i)) y =
      eqToHom (congrArg
          (fun Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) =>
            (Z.over U).val.obj (op (Over.mk i)))
          (show ((HomologicalComplex.single
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
              (ComplexShape.up ℤ) 0).obj N).X (n - n) = N from by rw [sub_self]; rfl))
        (applyHomSectionOver Y (sheafHomComplex Y E
          ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (ComplexShape.up ℤ) 0).obj N))
          U V i n (-n) (n - n) (by omega) s y) := by
  have := isIso_homDegreeProjection_single Y E N n
  rw [homDegreeIsoSingle, Iso.trans_hom, asIso_hom, eqToIso.hom, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    internalHomSheaf_eqToHom_target_app, homDegreeProjection_app_eq_applyHomSectionOver]
  rw [sub_self]
  rfl

end AlgebraicGeometry.RingedSite

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.Sites Stacks.SheafOfModules Stacks.RegularSequence

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}
  (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation]

/-- **The cochain-level identifications of the Ext sheaves are intertwined by pushforward along
the augmentation.** Going from the cohomology of the endomorphism complex `SheafHom^•(K, K)` to
the Ext sheaf, transporting the target along the augmentation, and coming back down to the
cohomology of `SheafHom^•(K, O_X[0])`, is the map induced on cohomology sheaves by pushforward
along the augmentation.

Three maps of Ext sheaves sit between the two identifications — the reindexing of the source
inverted, the pushforward, and the reindexing again — and they collapse to the pushforward alone;
what is left is an instance of naturality in the target. -/
theorem derivedSheafExtIsoHomologyCochain_augmentation (n : ℤ) :
    derivedSheafExtMap Rc n (𝟙 _)
          (DerivedCategory.Q.map (augSingle Rc K)) ≫
        (derivedSheafExtIsoHomologyCochain Rc K
          ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
            (quotient Rc (φ := φ))) n).hom =
      (derivedSheafExtIsoHomologyCochain Rc K (cochain Rc K) n).hom ≫
        HomologicalComplex.homologyMap (RingedSite.homMap (ringedSite Rc) (𝟙 (cochain Rc K))
          (augSingle Rc K)) n := by
  have hnat := Stacks.SheafOfModules.derivedSheafExtIsoHomologyOfResolution_naturality_target
    Rc (cochain Rc K) (cochain Rc K) n (finite_not_isZero_cochain_X Rc K)
    (isFiniteFreeSummand_cochain_X Rc K) (cochainAugmentation Rc K)
    (augSingle Rc K)
  let reindexing := (DerivedCategory.Q.mapIso (quotientSingleIso Rc (φ := φ))).hom
  let augmentation := DerivedCategory.Q.map (augSingle Rc K)
  have sourceSquare : derivedSheafExtMap Rc n (𝟙 _) augmentation ≫
      derivedSheafExtMap Rc n reindexing (𝟙 _) =
      derivedSheafExtMap Rc n reindexing (𝟙 _) ≫
        derivedSheafExtMap Rc n (𝟙 _) augmentation := by
    simp only [derivedSheafExtMap_comp, Category.comp_id, Category.id_comp]
  exact CategoryTheory.square_comp sourceSquare hnat

/-- The naturality square of `derivedSheafExtIsoHomologyCochain_augmentation` solved for the
pushforward: the cohomology of the endomorphism complex, carried up to the Ext sheaf, pushed
forward along the augmentation and carried back down, is the pushforward on cohomology sheaves.
This is the form in which `Stacks.RegularSequence.KoszulChainData.homIso` consumes it, that
identification beginning with the inverse of the cochain-level comparison. -/
theorem inv_comp_derivedSheafExtMap_augmentation (n : ℤ) :
    (derivedSheafExtIsoHomologyCochain Rc K (cochain Rc K) n).inv ≫
        derivedSheafExtMap Rc n (𝟙 _)
            (DerivedCategory.Q.map (augSingle Rc K)) ≫
          (derivedSheafExtIsoHomologyCochain Rc K
            ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
              (quotient Rc (φ := φ))) n).hom =
      HomologicalComplex.homologyMap (RingedSite.homMap (ringedSite Rc) (𝟙 (cochain Rc K))
        (augSingle Rc K)) n :=
  (congrArg ((derivedSheafExtIsoHomologyCochain Rc K (cochain Rc K) n).inv ≫ ·)
    (derivedSheafExtIsoHomologyCochain_augmentation Rc K n)).trans
      ((derivedSheafExtIsoHomologyCochain Rc K (cochain Rc K) n).inv_hom_id_assoc _)

/-- **The degree-`n` piece of the self-Ext algebra is identified with `SheafHom(K_n, O_X)` by
pushforward along the augmentation.** `Stacks.RegularSequence.KoszulChainData.homIso` is the
composite of three maps, all of them computable: the map on cohomology sheaves induced by
pushing a cochain of `SheafHom^•(K, K)` forward along the augmentation `K^• ⟶ O_X[0]`; the
identification of the cohomology of the resulting complex with its degree-`n` term, the
differentials of that complex vanishing; and the projection of that term onto its single
nonvanishing component, which evaluates on `K_n`.

So the class of a degree-`n` cocycle of `SheafHom^•(K, K)` goes to its component out of cochain
degree `-n` composed with the augmentation. This is the step of the proof of Stacks 0BQY that
replaces `Hom^•(A, A)` by `Hom^•(A, O_X)`.

Both derived-category comparisons inside `homIso` disappear: they are the cochain-level
identification at the endomorphism complex and at the complex concentrated in degree zero, and
the transport between them is pushforward along the augmentation by
`inv_comp_derivedSheafExtMap_augmentation`. -/
theorem homIso_hom (n : ℤ) :
    (homIso Rc K n).hom =
      HomologicalComplex.homologyMap (RingedSite.homMap (ringedSite Rc) (𝟙 (cochain Rc K))
            (augSingle Rc K)) n ≫
        (Stacks.CochainComplex.intHomologyIsoX _ (sheafHomComplex_d_eq_zero K) n).hom ≫
          (RingedSite.homDegreeIsoSingle (ringedSite Rc) (cochain Rc K)
              (quotient Rc (φ := φ)) n).hom ≫
            (eqToIso (congrArg (fun M => RingedSite.internalHomSheaf (ringedSite Rc) M
              (quotient Rc (φ := φ))) (congrArg K.chain.X (neg_neg n)))).hom := by
  have haug : (asIso (DerivedCategory.Q.map (cochainAugmentation Rc K))).hom ≫
        (DerivedCategory.Q.mapIso (quotientSingleIso Rc (φ := φ))).hom =
      DerivedCategory.Q.map (augSingle Rc K) := by
    rw [augSingle, CategoryTheory.Functor.map_comp]
    rfl
  dsimp only [homIso, extIsoInternalHom, Iso.trans, Iso.symm,
    derivedSheafExtMapIso, Iso.refl]
  simp only [haug]
  refine (congrArg ((derivedSheafExtIsoHomologyCochain Rc K (cochain Rc K) n).inv ≫ ·)
    (Category.assoc _ _ _).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) (inv_comp_derivedSheafExtMap_augmentation Rc K n)

/-- **The self-Ext identification, on the class of a cocycle.** Precomposed with the projection
onto cohomology, `Stacks.RegularSequence.KoszulChainData.homIso` is: include the cocycle into the
internal endomorphism complex, push it forward along the augmentation, and project onto the
degree-`n` component. So the class of a degree-`n` cocycle of `SheafHom^bullet(K, K)` is carried to
that cocycle's component composed with the augmentation, no cohomology class and no
derived-category object appearing on the right.

The three steps of `homIso_hom` each lose their cohomology class in turn: the pushforward on
cohomology sheaves commutes with the projection onto cohomology
(`CategoryTheory.HomologicalComplex.homologyπ_naturality`); the identification of the cohomology
of a complex with vanishing differentials with its degree-`n` term carries a class to its cycle
(`Stacks.CochainComplex.homologyπ_comp_intHomologyIsoX_hom`); and the inclusion of the cycles
commutes with the pushforward (`CategoryTheory.HomologicalComplex.cyclesMap_i`). -/
theorem homologyπ_comp_homIso_hom (n : ℤ) :
    (endComplex Rc (cochain Rc K)).homologyπ n ≫ (homIso Rc K n).hom =
      (endComplex Rc (cochain Rc K)).iCycles n ≫
        (RingedSite.homMap (ringedSite Rc) (𝟙 (cochain Rc K))
            (augSingle Rc K)).f n ≫
          (RingedSite.homDegreeIsoSingle (ringedSite Rc) (cochain Rc K)
              (quotient Rc (φ := φ)) n).hom ≫
            (eqToIso (congrArg (fun M => RingedSite.internalHomSheaf (ringedSite Rc) M
              (quotient Rc (φ := φ))) (congrArg K.chain.X (neg_neg n)))).hom := by
  rw [homIso_hom]
  refine (HomologicalComplex.homologyπ_naturality_assoc
    (RingedSite.homMap (ringedSite Rc) (𝟙 (cochain Rc K)) (augSingle Rc K)) n _).trans ?_
  refine (congrArg (HomologicalComplex.cyclesMap
    (RingedSite.homMap (ringedSite Rc) (𝟙 (cochain Rc K)) (augSingle Rc K)) n ≫ ·)
    (Stacks.CochainComplex.homologyπ_comp_intHomologyIsoX_hom_assoc
      _ (sheafHomComplex_d_eq_zero K) n _)).trans ?_
  exact HomologicalComplex.cyclesMap_i_assoc
    (RingedSite.homMap (ringedSite Rc) (𝟙 (cochain Rc K)) (augSingle Rc K)) n _

/-- `Stacks.RegularSequence.KoszulChainData.homologyπ_comp_homIso_hom` read on local sections: the
identification carries the class over `U` of a degree-`n` cocycle `z` to the degree-`n` component
of `z`, pushed forward along the augmentation. -/
theorem homIso_hom_val_app_homologyπ (n : ℤ) (U : (Opens ↥X)ᵒᵖ)
    (z : ((endComplex Rc (cochain Rc K)).cycles n).val.obj U) :
    (homIso Rc K n).hom.val.app U
        (((endComplex Rc (cochain Rc K)).homologyπ n).val.app U z) =
      (eqToIso (congrArg (fun M => RingedSite.internalHomSheaf (ringedSite Rc) M
            (quotient Rc (φ := φ))) (congrArg K.chain.X (neg_neg n)))).hom.val.app U
        ((RingedSite.homDegreeIsoSingle (ringedSite Rc) (cochain Rc K)
              (quotient Rc (φ := φ)) n).hom.val.app U
          (((RingedSite.homMap (ringedSite Rc) (𝟙 (cochain Rc K))
                (augSingle Rc K)).f n).val.app U
            (((endComplex Rc (cochain Rc K)).iCycles n).val.app U z))) :=
  congrFun (congrArg (fun g => ⇑(ConcreteCategory.hom
    ((_root_.SheafOfModules.Hom.val g).app U))) (homologyπ_comp_homIso_hom Rc K n)) z

/-- **The self-Ext identification, evaluated.** The class over `U` of a degree-`n` cocycle `z` of
`SheafHom^bullet(K, K)` is carried by `homIso` to the homomorphism `K_n ⟶ O_X` which, on a section
`y` of `K_n` over an arrow `i : V ⟶ U`, takes the value obtained by applying the `(-n, n - n)`
component of `z` to `y` and then the augmentation.

This is `Stacks.RegularSequence.KoszulChainData.homIso_hom_val_app_homologyπ` with each of its
three factors evaluated: the two transports of an internal Hom sheaf by
`AlgebraicGeometry.RingedSite.internalHomSheaf_eqToHom_source_app` and
`AlgebraicGeometry.RingedSite.homDegreeIsoSingle_app_apply`, and the pushforward by
`AlgebraicGeometry.RingedSite.applyHomSectionOver_homMap`. Nothing of the Hom complex is left on
the right beyond a single component of the cocycle, so a computation that knows the components of
`z` — as `Stacks.RegularSequence.KoszulChainData.applyHomSectionOver_iteratedContractionSection`
does for the iterated contraction — knows the value of the identification on its class.

The two transports are those of `homIso` itself: the source one identifies the degree `-n` term of
the Koszul cochain complex with the degree-`n` term of the chain complex, and the target one
identifies the degree `n - n` term of the complex concentrated in degree zero with the quotient.

**Both are transports of section types rather than morphisms of sheaves, and a consumer that needs
to cancel one against another transport must convert first**, by
`Stacks.SheafOfModules.eqToHom_over_val_app`. A transport of types is a `cast` and composes with
nothing; the sheaf-level `eqToHom` it corresponds to composes by `CategoryTheory.eqToHom_trans`.
The type-level form is what appears here because the statement evaluates a section, and
restating it in sheaf-level form would not remove the transports — they are intrinsic to
`AlgebraicGeometry.RingedSite.homDegreeIsoSingle`, whose target is the internal Hom sheaf into the
degree `n - n` term of a complex concentrated in degree zero. The morphism-level companion
`homologyπ_comp_homIso_hom` is transport-free on the left and carries its transports as genuine
`eqToHom`s, so a computation that must cancel them should start from that one. -/
theorem homIso_app_apply (n : ℤ) (U V : Opens ↥X) (i : V ⟶ U)
    (z : ((endComplex Rc (cochain Rc K)).cycles n).val.obj (op U))
    (y : (((K.chain.X n)).over U).val.obj (op (Over.mk i))) :
    ((homIso Rc K n).hom.val.app (op U)
          (((endComplex Rc (cochain Rc K)).homologyπ n).val.app (op U) z)).app
        (op (Over.mk i)) y =
      eqToHom (congrArg
          (fun Z : StructureSheafModules Rc => (Z.over U).val.obj (op (Over.mk i)))
          (show ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
              (quotient Rc (φ := φ))).X (n - n) = quotient Rc (φ := φ) from
            by rw [sub_self]; rfl))
        (((augSingle Rc K).f (n - n)).val.app (op V)
          (RingedSite.applyHomSectionOver (ringedSite Rc)
            (RingedSite.sheafHomComplex (ringedSite Rc) (cochain Rc K) (cochain Rc K))
            U V i n (-n) (n - n) (by omega)
            (((endComplex Rc (cochain Rc K)).iCycles n).val.app (op U) z)
            (eqToHom (congrArg
              (fun Z : StructureSheafModules Rc => (Z.over U).val.obj (op (Over.mk i)))
              (congrArg K.chain.X (neg_neg n)).symm) y))) := by
  rw [homIso_hom_val_app_homologyπ, eqToIso.hom]
  refine Eq.trans (AlgebraicGeometry.RingedSite.internalHomSheaf_eqToHom_source_app
    (ringedSite Rc) (quotient Rc (φ := φ)) (congrArg K.chain.X (neg_neg n)) _ U _
    (op (Over.mk i)) y) ?_
  refine Eq.trans (AlgebraicGeometry.RingedSite.homDegreeIsoSingle_app_apply
    (ringedSite Rc) (cochain Rc K) (quotient Rc (φ := φ)) n U V i _ _) ?_
  refine congrArg _ ?_
  exact RingedSite.applyHomSectionOver_homMap (ringedSite Rc) (𝟙 (cochain Rc K))
    (augSingle Rc K) U V i n (-n) (n - n) (by omega) _ _

/-- **The self-Ext identification on the iterated-contraction class.** For a tuple
`f : Fin (i+1) → {1, …, r}` of coordinates, the class of the `(i+1)`-fold composite of the
coordinate contractions is carried by `homIso` to the homomorphism `K_{i+1} ⟶ O_X` given by the
iterated contraction `K.tupleCoordKoszulDOf` followed by the augmentation.

This is `Stacks.RegularSequence.KoszulChainData.homIso_app_apply` at the iterated-contraction
cocycle, whose components are
`Stacks.RegularSequence.KoszulChainData.applyHomSectionOver_iteratedContractionSection`. It is the
cocycle half of the local computation of Stacks 0BQY transported out of the cohomology of
`SheafHom^bullet(K, K)` and into a module of homomorphisms, which is where the stalk computation
can meet it. -/
theorem homIso_app_apply_iteratedContractionClassOn (i : ℕ)
    (f : Fin (i + 1) → ULift.{u} (Fin r)) (U V : Opens ↥X) (g : V ⟶ U)
    (y : ((K.chain.X ((i + 1 : ℕ) : ℤ)).over U).val.obj (op (Over.mk g))) :
    ((homIso Rc K ((i + 1 : ℕ) : ℤ)).hom.val.app (op U)
          (iteratedContractionClassOn Rc K i f (op U))).app (op (Over.mk g)) y =
      eqToHom (congrArg
          (fun Z : StructureSheafModules Rc => (Z.over U).val.obj (op (Over.mk g)))
          (show ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
              (quotient Rc (φ := φ))).X (((i + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ))
              = quotient Rc (φ := φ) from by rw [sub_self]; rfl))
        (((augSingle Rc K).f
              (((i + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ))).val.app (op V)
          ((K.tupleCoordKoszulDOf (i + 1) (fun k => f k.rev)
              (show -(((i + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ)) + ((i + 1 : ℕ) : ℤ)
                = -(-((i + 1 : ℕ) : ℤ)) by omega)).val.app (op V)
            (eqToHom (congrArg
              (fun Z : StructureSheafModules Rc => (Z.over U).val.obj (op (Over.mk g)))
              (congrArg K.chain.X (neg_neg ((i + 1 : ℕ) : ℤ))).symm) y))) := by
  refine Eq.trans (homIso_app_apply Rc K ((i + 1 : ℕ) : ℤ) U V g
    ((iteratedContractionCycle Rc K i f).val.app (op U)
      (1 : (structureSheaf Rc).obj.obj (op U))) y) ?_
  refine congrArg _ (congrArg _ ?_)
  refine Eq.trans (congrArg
    (fun w => RingedSite.applyHomSectionOver (ringedSite Rc) (endHom Rc K) U V g
      ((i + 1 : ℕ) : ℤ) (-((i + 1 : ℕ) : ℤ))
      (((i + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ)) (by omega) w _)
    (iCycles_iteratedContractionCycle Rc K i f (op U))) ?_
  exact applyHomSectionOver_iteratedContractionSection Rc K i f U V g
    (-((i + 1 : ℕ) : ℤ)) (((i + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ)) (by omega) _

end Stacks.RegularSequence.KoszulChainData

end
