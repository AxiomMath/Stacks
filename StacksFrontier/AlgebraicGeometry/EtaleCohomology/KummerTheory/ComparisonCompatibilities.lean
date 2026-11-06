module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRightScalar
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairComparisonHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TrivializationTorsorPicard
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.UnitPairTorsor
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Pushforward
public import StacksFrontier.AlgebraicGeometry.Picard.MultiplicativeGroupFirstCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsAndPushforward

/-!
# The comparison map of Tag 040Q is a map of extensions at both ends

Tag 040Q identifies the isomorphism classes of pairs `(ℒ, α)` on a scheme `S` with
`H¹((Sch/S)_τ, μ_n)`, and the identification is a map between two presentations of those groups
as extensions of the `n`-torsion of `Pic(S)` by the global units modulo `n`-th powers.  The
comparison homomorphism is `AlgebraicGeometry.basePairCohomologyClassHom`; the pair side of the
extension is `AlgebraicGeometry.pairSheafClassHom` and `AlgebraicGeometry.unitPairHom`, and the
cohomological side is the map `H¹(μ_n) ⟶ H¹(𝐆_m) = Pic(S)` and
`AlgebraicGeometry.kummerBoundary`.

This file proves both compatibilities.  On the **right-hand** end the composite of the comparison
with `H¹(μ_n) ⟶ H¹(𝐆_m) = Pic(S)` is the Picard class of the invertible sheaf of the pair.  On the
**left-hand** end the comparison carries the class of the pair `(𝒪_S, f)` of a global unit `f` to
`-AlgebraicGeometry.kummerBoundary f`; with these two in hand
`Stacks.Kummer.bijective_of_comparison` proves Tag 040Q in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Comparison040Q`.

## Main definitions

* `AlgebraicGeometry.basePairPicardHom`: the right-hand map of the cohomological side,
  `H¹((Sch/S)_τ, μ_n) →+ Pic(S)`, as a homomorphism of abelian groups: the map induced by the
  inclusion `μ_n ⟶ 𝐆_m` followed by the identification of Tag 03P8.

## Main results

* `AlgebraicGeometry.basePairCohomologyClass_picard`: **the comparison map of Tag 040Q is
  compatible with the Picard group**, read on the class of a pair.
* `AlgebraicGeometry.basePairPicardHom_basePairCohomologyClassHom`: the same as an identity of
  the two homomorphisms out of the group of isomorphism classes of pairs.  This is the
  hypothesis `hrc` of `Stacks.Kummer.bijective_of_comparison`.
* `AlgebraicGeometry.baseAssociatedModule_map_scalarEnd`: **the associated-module functor of
  Descent, Proposition 03DX carries multiplication by a global function of `S` to multiplication
  by that same function**, read over the terminal object `S / S` of the big `τ`-site.
* `AlgebraicGeometry.scalarEndOfTerminal_unitEndSection`,
  `AlgebraicGeometry.exists_scalarIsoOfTerminal` and
  `AlgebraicGeometry.scalarEndOfTerminal_naturality`: on a ringed site with a terminal object,
  every endomorphism of the structure sheaf as a module over itself is multiplication by a
  section over that object, every automorphism by a unit of those sections, and multiplication
  by a section is natural in the sheaf of modules.
* `AlgebraicGeometry.exists_unitPairTrivialization_eq_basePairTriv`: **the transported
  trivialization of the unit pair at a global unit `f` is the site-level
  `Stacks.Cohomology.Torsors.Generators.unitPairTrivialization` at `c * f`**, for one global
  unit `c` independent of `f`.
* `AlgebraicGeometry.basePairCohomologyClass_unitPair`: **the comparison map of Tag 040Q is
  compatible with the left-hand end of the two extensions.**  This is the hypothesis `hci` of
  `Stacks.Kummer.bijective_of_comparison`.

## Implementation notes

The right-hand compatibility is already in the library in two halves and they compose with no
computation.
`AlgebraicGeometry.trivializationTorsor_firstCohomologyMap` says that `H¹(μ_n) ⟶ H¹(𝐆_m)`
carries the class of the torsor of trivializations of a pair to the class of the torsor of local
generators of its invertible module, and
`Stacks.Picard.AllTopologies.baseH1UnitsAddEquivSchemePicardGroup_symm_classOf` says that the
identification of Tag 03P8 carries the Picard class of an invertible `𝒪_S`-module to the class of
the torsor of local generators of its associated module.  The two torsors are the same term:
`AlgebraicGeometry.basePairSheaf` *is* the associated module of the invertible sheaf of the pair,
the two invertibility hypotheses are proofs of one proposition, and the sheaf of units of the
ringed site is the sheaf of units of the functor by
`AlgebraicGeometry.unitsAddSheaf_schemeFunctionsRingedSite`.

This module is a leaf: the two halves live in import closures that do not contain one another,
and joining them inside
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairComparisonHom` would add 208
modules to the closure of that file and of everything downstream of it.  Placed here the edge
costs nothing to any existing consumer.

The left-hand compatibility is not a monoidal identity and so is not of the shape of
`Stacks.SheafOfModules.TensorPowerTransport.transportTriv_tensor`: what it needs is the action of
the associated-module functor on multiplication by a global section.  The functor is a pullback
and has no formula on morphisms, so that action is obtained from the corresponding identity for
the pushforward through `CategoryTheory.Adjunction.map_endOfId`, which is
`AlgebraicGeometry.baseAssociatedModule_map_scalarEnd`.  The twisting unit `c` of
`AlgebraicGeometry.exists_unitPairTrivialization_eq_basePairTriv` is not computed; it is produced
by `AlgebraicGeometry.exists_scalarIsoOfTerminal` and then killed by reading the statement at
`f = 1`, where the class of the unit pair is zero.

Every crossing between the two spellings of the structure sheaf of the big `τ`-site is a separate
declaration, and the reassociations of composites of isomorphisms are stated for an arbitrary
category.  Carried as `have`s inside one proof the recursion is counted on top of the enclosing
elaboration and the last crossing exceeds the `whnf` budget; `maxHeartbeats` is not an option
here.

## References

* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8)
* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.Torsors (torsorSetoid torsorIsoClassesEquivH1)
open Stacks.Cohomology.Torsors.Generators (LocalRoots)
open Stacks.SheafOfModules.Picard (PicardGroup)
open Stacks.Cohomology.Torsors.Generators (scalarEndOfTerminal scalarIsoOfTerminal
  unitPowerTrivialization unitPairTrivialization isInvertible_unit_ringSheaf tpow powerMap)
open Stacks.Cohomology.SiteModules (unitEnd unitEndSection)
open Stacks.SheafOfModules.TensorPowerTransport (powerTransportIso)

universe v₁ v₂ v₃ u u₃

namespace AlgebraicGeometry

/-! ### Two reassociations of composites of isomorphisms

Both move an automorphism from the inside of a composite of isomorphisms to its right-hand end.
They are stated for an arbitrary category and proved on underlying morphisms, where the terms are
small; carried out inline on the composites of §"The transport of the unit pair" below, the same
reassociations are what overflows the `whnf` budget. -/

section Reassoc

variable {D : Type u₃} [Category.{v₃} D]

/-- A composite of three isomorphisms whose last factor is an automorphism commuting with a
fourth, written with that automorphism moved past the fourth to the right-hand end. -/
private theorem trans_trans_comm {W V P Q : D} (g : W ≅ V) (m : V ≅ P) (a : P ≅ P) (u : P ≅ Q)
    (b : Q ≅ Q) (h : a ≪≫ u = u ≪≫ b) :
    (g ≪≫ m ≪≫ a) ≪≫ u = ((g ≪≫ m) ≪≫ u) ≪≫ b :=
  have h' : a.hom ≫ u.hom = u.hom ≫ b.hom := congrArg Iso.hom h
  Iso.ext (by simp only [Iso.trans_hom, Category.assoc, h'])

/-- A composite of four isomorphisms whose third factor is the inverse of the first two followed
by a fifth, with the first two cancelled. -/
private theorem trans_trans_cancel {L N M : D} (p : L ≅ N) (q : N ≅ M) (a r : M ≅ M) (G : L ≅ M)
    (h : a = (p ≪≫ q).symm ≪≫ G) : p ≪≫ q ≪≫ a ≪≫ r = G ≪≫ r := by
  subst h
  exact Iso.ext (by simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
    Iso.hom_inv_id_assoc])

end Reassoc

/-! ### Endomorphisms of the structure sheaf of a ringed site as a module over itself

The three statements of this section are about an arbitrary ringed site with a terminal object.
Their natural home is beside `Stacks.Cohomology.Torsors.Generators.scalarIsoOfTerminal`; they are
here because that is a mid-tree module and this one is a leaf. -/

section RingedSite

variable (X : RingedSite.{v₁, v₂, u}) [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] {T : X.C} (hT : Limits.IsTerminal T)

-- The commutativity of the sections of the structure sheaf, which multiplication by a global
-- section asks for, is `local` where it is declared, so the attribute is re-enabled here rather
-- than the instance restated.
attribute [local instance] Stacks.Cohomology.Torsors.Generators.ringSections_isMulCommutative

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}] in
/-- **Every endomorphism of the structure sheaf of a ringed site, viewed as a module over
itself, is multiplication by a section over a terminal object** — by its own value at the
section one there.  This is `Stacks.Cohomology.SiteModules.unitEndEquiv` read at a terminal
object, where a compatible family of sections is the restriction of its value there. -/
public theorem scalarEndOfTerminal_unitEndSection
    (g : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    scalarEndOfTerminal X hT
        ((unitEndSection (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).1 (op T))
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = g := by
  have hsec : unitEndSection (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (scalarEndOfTerminal X hT
          ((unitEndSection (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).1 (op T))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) =
        unitEndSection (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g := by
    refine Subtype.ext (funext fun Z => ?_)
    refine Eq.trans ?_
      ((unitEndSection (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).2 (hT.from Z.unop).op)
    refine Eq.trans (Stacks.Cohomology.Torsors.Generators.scalarEndOfTerminal_app X hT
      ((unitEndSection (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).1 (op T))
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) Z.unop
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj Z)) ?_
    exact mul_one _
  refine Eq.trans (Stacks.Cohomology.SiteModules.unitEnd_unitEndSection
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) _).symm ?_
  exact Eq.trans (congrArg (unitEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) hsec)
    (Stacks.Cohomology.SiteModules.unitEnd_unitEndSection
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}] in
/-- **An automorphism of the structure sheaf of a ringed site with a terminal object is
multiplication by a unit of the sections over that object.** -/
public theorem exists_scalarIsoOfTerminal
    (e : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ∃ c : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T) : Type u)ˣ,
      scalarIsoOfTerminal X hT c
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = e := by
  have key : ∀ a b : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      a ≫ b = 𝟙 _ → (unitEndSection (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).1 (op T) *
        (unitEndSection (Stacks.SheafOfModules.Tensor.ringSheaf X.O) b).1 (op T) = 1 := by
    intro a b hab
    have h := Stacks.Cohomology.SiteModules.unitEndSection_comp
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a b
    rw [hab, Stacks.Cohomology.SiteModules.unitEndSection_id] at h
    exact congrArg
      (fun z : RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =>
        z.1 (op T)) h.symm
  refine ⟨⟨(unitEndSection (Stacks.SheafOfModules.Tensor.ringSheaf X.O) e.hom).1 (op T),
    (unitEndSection (Stacks.SheafOfModules.Tensor.ringSheaf X.O) e.inv).1 (op T),
    key _ _ e.hom_inv_id, key _ _ e.inv_hom_id⟩, ?_⟩
  exact Iso.ext (scalarEndOfTerminal_unitEndSection X hT e.hom)

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}] in
/-- Multiplication by two sections over a terminal object composes to multiplication by their
product. -/
public theorem scalarIsoOfTerminal_trans
    (a b : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T) : Type u)ˣ)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    scalarIsoOfTerminal X hT a M ≪≫ scalarIsoOfTerminal X hT b M =
      scalarIsoOfTerminal X hT (a * b) M :=
  Iso.ext (Stacks.Cohomology.Torsors.Generators.scalarEndOfTerminal_mul X hT a.val b.val M)

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}] in
/-- **Multiplication by a section over a terminal object is natural in the sheaf of modules.**
It is the value at that sheaf of an endomorphism of the identity functor,
`Stacks.SheafOfModules.terminalSectionToEnd`, so this is that naturality read backwards. -/
public theorem scalarEndOfTerminal_naturality
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T))
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : M ⟶ N) :
    scalarEndOfTerminal X hT r M ≫ g = g ≫ scalarEndOfTerminal X hT r N :=
  ((Stacks.SheafOfModules.terminalSectionToEnd
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) T hT r).asHom.naturality g).symm

end RingedSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (τ : SiteKind) (n : ℕ)

-- The two sheafification retypings that `AlgebraicGeometry.trivializationTorsor` needs at the
-- `(schemeFunctionsRingedSite _ _ _).J` spelling are `local` where they are declared, so the
-- attribute is re-enabled here rather than either of them restated.
attribute [local instance] baseSchemeFunctions_hasWeakSheafify
  baseSchemeFunctions_wEqualsLocallyBijective basePairSheafObj_isInvertible

variable [∀ σ : SiteKind, HasSheafify (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u}]
  [∀ σ : SiteKind, HasExt.{u} (Sheaf (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u})]

/-- **The right-hand map of the cohomological side of Tag 040Q**, `H¹((Sch/S)_τ, μ_n) →+ Pic(S)`:
the map induced on first cohomology by the inclusion `μ_n ⟶ 𝐆_m` of the Kummer sequence,
followed by the identification `H¹_τ(S, 𝐆_m) = Pic(S)` of Tag 03P8.  Both factors are already
homomorphisms: `CategoryTheory.Sheaf.H.map` is one and the identification is an `AddEquiv`. -/
public def basePairPicardHom :
    Sheaf.H (rootsOfUnitySheaf (BigFppfOver.baseOverTopology B S hS τ)
        (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n) 1 →+
      PicardGroup S.presheaf (ringSheafCond S) :=
  (Stacks.Picard.AllTopologies.baseH1UnitsAddEquivSchemePicardGroup B S hS
      τ).toAddMonoidHom.comp
    (Sheaf.H.map (kernel.ι (powerSheaf (BigFppfOver.baseOverTopology B S hS τ)
      (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n)) 1)

/-- **The comparison map of Tag 040Q is compatible with the Picard group**, read on the class of
a pair: the image of the class of a pair `(ℒ, α)` in `H¹((Sch/S)_τ, μ_n)` is carried by
`H¹(μ_n) ⟶ H¹(𝐆_m) = Pic(S)` to the Picard class of `ℒ`.

This is `AlgebraicGeometry.trivializationTorsor_firstCohomologyMap` followed by
`Stacks.Picard.AllTopologies.baseH1UnitsAddEquivSchemePicardGroup_symm_classOf`. -/
@[stacks 040Q "the comparison map from the isomorphism classes of pairs to H^1 of the roots of \
unity is compatible with the right-hand end of the two extensions: composed with the map to H^1 \
of the multiplicative group and the identification of that with the Picard group (Tag 03P8) it \
is the Picard class of the invertible sheaf of the pair. Injectivity and surjectivity of the \
comparison are not proved here, nor is the compatibility with the left-hand end"]
public theorem basePairCohomologyClass_picard
    (hroot : LocalRoots (BigFppfOver.baseRingedSite B S hS τ) n) (P : TrivializedPower S n) :
    Stacks.Picard.AllTopologies.baseH1UnitsAddEquivSchemePicardGroup B S hS τ
        (Sheaf.H.map (kernel.ι (powerSheaf (BigFppfOver.baseOverTopology B S hS τ)
            (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n)) 1
          (basePairCohomologyClassHom B S hS τ n hroot (pairClass P))) =
      pairSheafClassHom S n (pairClass P) := by
  have h1 := trivializationTorsor_firstCohomologyMap
    (BigFppfOver.baseOverTopology B S hS τ) (BigFppfOver.toScheme B S hS)
    (BigFppfOver.baseRingedSite B S hS τ).O.property (unitsPresheaf_isSheaf_base B S hS τ) n
    (baseRingedSite_isLocallyRinged B S hS τ) hroot (basePairSheaf B S hS τ n P)
    (basePairSheaf_isInvertible B S hS τ n P) (basePairTriv B S hS τ n P)
  have h2 := Stacks.Picard.AllTopologies.baseH1UnitsAddEquivSchemePicardGroup_symm_classOf
    B S hS τ P.sheaf P.invertible
  exact (congrArg _ h1).trans ((congrArg _ h2).symm.trans (AddEquiv.apply_symm_apply _ _))

/-- **The comparison homomorphism of Tag 040Q is a map of extensions on the right**: composing it
with the right-hand map of the cohomological side gives the right-hand map of the pair side.

This is `AlgebraicGeometry.basePairCohomologyClass_picard` read on the whole group of isomorphism
classes of pairs, and it is the hypothesis `hrc` of
`Stacks.Kummer.bijective_of_comparison`.

Tag 040Q itself is registered on `AlgebraicGeometry.pairClassesAddEquivH1Etale` and its fppf and
syntomic companions. -/
public theorem basePairPicardHom_basePairCohomologyClassHom
    (hroot : LocalRoots (BigFppfOver.baseRingedSite B S hS τ) n) (x : PairClasses S n) :
    basePairPicardHom B S hS τ n (basePairCohomologyClassHom B S hS τ n hroot x) =
      pairSheafClassHom S n x :=
  Quotient.inductionOn x fun P => basePairCohomologyClass_picard B S hS τ n hroot P

/-! ### The transport of multiplication by a global function -/

omit [∀ σ : SiteKind, HasSheafify (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u}]
  [∀ σ : SiteKind,
    HasExt.{u} (Sheaf (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u})] in
/-- **The associated-module functor carries multiplication by a global function of `S` to
multiplication by that same global function**, read over the terminal object `S / S` of the big
`τ`-site.

The functor is the pullback along the morphism of ringed sites `((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)`,
for which there is no formula on morphisms; the identity is obtained from the corresponding one
for the *pushforward*, `Stacks.SheafOfModules.map_globalSectionToEnd`, through
`CategoryTheory.Adjunction.map_endOfId`.  Its hypothesis is the square saying that the structure
map of the morphism of sites carries the restrictions of `s` from the top open of `S` to the
restrictions of `s` from `S / S`, and over the top open that map is the identification
`Γ(S, ⊤) = Γ(⊤, ⊤)`. -/
@[stacks 040Q "the associated-module functor of Descent, Proposition 03DX carries \
multiplication by a global function of the base to multiplication by that same function over \
the terminal object of the big tau-site; this is one ingredient of the compatibility of the \
comparison map with the left-hand end of the two extensions, and neither that compatibility \
nor any other part of the tag is proved here"]
public theorem baseAssociatedModule_map_scalarEnd
    (hT : IsTerminal (C := BigFppfOver B S hS) (Over.mk (𝟙 (B.obj hS))))
    (s : Scheme.Γ.obj (op S)) (M : SheafOfModules.{u} (ringSheaf S)) :
    (BigFppfOver.baseAssociatedModule B S hS τ).map (scalarEnd S s M) =
      Stacks.Cohomology.Torsors.Generators.scalarEndOfTerminal
        (BigFppfOver.baseRingedSite B S hS τ) hT s
        ((BigFppfOver.baseAssociatedModule B S hS τ).obj M) := by
  let : ∀ U, IsMulCommutative ((FibredSite.baseRingStructureSheaf B S hS τ).obj.obj U) :=
    fun U => inferInstanceAs
      (IsMulCommutative ((BigFppfOver.baseRingedSite B S hS τ).O.obj.obj U))
  let : ∀ U, IsMulCommutative (S.ringCatSheaf.obj.obj U) :=
    fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))
  refine CategoryTheory.Adjunction.map_endOfId
    (BigFppfOver.baseAssociatedModuleAdjunction B S hS τ) (fun N => ?_) M
  refine Stacks.SheafOfModules.map_globalSectionToEnd (BigFppfOver.baseStructureMap B S hS τ)
    (Stacks.SheafOfModules.terminalSection
      (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O)
      (Over.mk (𝟙 (B.obj hS))) hT s)
    (Stacks.SheafOfModules.terminalSection (ringSheaf S) ⊤ Limits.isTerminalTop s) ?_ N
  intro U
  show (BigFppfOver.baseStructureMap B S hS τ).hom.app U
      ((ringSheaf S).obj.map (Limits.isTerminalTop.from U.unop).op s) =
    (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).obj.map
      (hT.from ((BigFppfOver.opensToBig B S hS).obj U.unop)).op s
  have hfrom : hT.from ((BigFppfOver.opensToBig B S hS).obj U.unop) =
      (BigFppfOver.opensToBig B S hS).map (Limits.isTerminalTop.from U.unop) ≫
        hT.from ((BigFppfOver.opensToBig B S hS).obj ⊤) := hT.hom_ext _ _
  have hkey : (BigFppfOver.baseStructureMap B S hS τ).hom.app (op ⊤) =
      (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).obj.map
        (hT.from ((BigFppfOver.opensToBig B S hS).obj ⊤)).op := by
    rw [hT.hom_ext (hT.from ((BigFppfOver.opensToBig B S hS).obj ⊤))
      (Over.mkIdTerminal.from ((BigFppfOver.opensToBig B S hS).obj ⊤)),
      BigFppfOver.baseStructureMap_hom_app]
    have h0 : (BigFppfOver.toScheme B S hS).map
        (Over.mkIdTerminal.from ((BigFppfOver.opensToBig B S hS).obj ⊤)) = (⊤ : S.Opens).ι := by
      show B.inclusion.map
        (Over.mkIdTerminal.from ((BigFppfOver.opensToBig B S hS).obj ⊤)).left = _
      rw [Over.mkIdTerminal_from_left]
      rfl
    show (forget₂ CommRingCat RingCat).map ((⊤ : S.Opens).topIso.inv) =
      (forget₂ CommRingCat RingCat).map (Scheme.Γ.map
        ((BigFppfOver.toScheme B S hS).map
          (Over.mkIdTerminal.from ((BigFppfOver.opensToBig B S hS).obj ⊤))).op)
    rw [h0]
    exact congrArg (forget₂ CommRingCat RingCat).map (CommRingCat.hom_ext rfl)
  refine Eq.trans (NatTrans.naturality_apply
    (BigFppfOver.baseStructureMap B S hS τ).hom (Limits.isTerminalTop.from U.unop).op s) ?_
  show (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).obj.map
      ((BigFppfOver.opensToBig B S hS).map (Limits.isTerminalTop.from U.unop)).op
      ((BigFppfOver.baseStructureMap B S hS τ).hom.app (op ⊤) s) = _
  rw [hkey]
  refine Eq.trans (Functor.map_comp_apply
    (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).obj
    (hT.from ((BigFppfOver.opensToBig B S hS).obj ⊤)).op
    ((BigFppfOver.opensToBig B S hS).map (Limits.isTerminalTop.from U.unop)).op s).symm ?_
  rw [hfrom, op_comp]

/-! ### The transport of the unit pair

The statements below identify the transported trivialization
`AlgebraicGeometry.basePairTriv` of the unit pair at a global unit `f` of `S` with the site-level
`Stacks.Cohomology.Torsors.Generators.unitPairTrivialization` at `c * f`, for one global unit `c`
independent of `f`.  That `c` is not computed: the two trivializations differ by an automorphism
of the structure sheaf of the big `τ`-site, and
`AlgebraicGeometry.exists_scalarIsoOfTerminal` says every such automorphism is multiplication by
a unit of the sections over the terminal object.  What has to be proved is that the difference
does not depend on `f`, which is the content of
`AlgebraicGeometry.basePairTriv_unitPair_eq`: the functor carries multiplication by `f` to
multiplication by `f`, by `AlgebraicGeometry.baseAssociatedModule_map_scalarEnd`, and
multiplication by a section over a terminal object is natural, so the twist comes out of the
composite on the right.

Each crossing between the two spellings is a separate declaration rather than a `have`: as
`have`s inside one proof the recursion is counted on top of the enclosing elaboration and the
last of them exceeds the `whnf` budget. -/

/-- The structure sheaf of the big `τ`-site is invertible as a module over itself, at the
spelling the tensor powers of `Stacks.Cohomology.Torsors.Generators.powerMap` ask for.
`Stacks.Cohomology.Torsors.Generators.isInvertible_unit_ringSheaf` is indexed at
`Stacks.SheafOfModules.Tensor.ringSheaf`, an abbreviation for
`AlgebraicGeometry.SheafOfModules.underlyingRingSheafOfSite`, while the tensor powers ask at
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`; the two sheaves of rings are the
same, but the instance keys are not, so the instance is not found at that spelling. -/
local instance isInvertible_unit_baseRingSheaf :
    Stacks.SheafOfModules.IsInvertible (BigFppfOver.baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (BigFppfOver.baseRingedSite B S hS τ).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2)) :=
  isInvertible_unit_ringSheaf (BigFppfOver.baseRingedSite B S hS τ)

/-- The associated module of the structure sheaf of `S` is invertible, at the spelling the tensor
powers of `Stacks.Cohomology.Torsors.Generators.powerMap` ask for: the module written as the value
of the functor at `SheafOfModules.unit`, rather than as `AlgebraicGeometry.basePairSheaf` of a
pair, which is the shape `AlgebraicGeometry.basePairSheafObj_isInvertible` matches. -/
local instance baseAssociatedModuleUnit_isInvertible :
    Stacks.SheafOfModules.IsInvertible (BigFppfOver.baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2
      ((BigFppfOver.baseAssociatedModule B S hS τ).obj (SheafOfModules.unit (ringSheaf S))) :=
  Stacks.SheafOfModules.TensorPowerTransport.isInvertible_obj S.presheaf (ringSheafCond S)
    (BigFppfOver.baseRingedSite B S hS τ).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2
    (BigFppfOver.baseAssociatedModule B S hS τ)
    (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ)
    (BigFppfOver.baseAssociatedModuleTensorIso' B S hS τ) (SheafOfModules.unit (ringSheaf S))

omit [∀ σ : SiteKind, HasSheafify (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u}]
  [∀ σ : SiteKind,
    HasExt.{u} (Sheaf (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u})] in
/-- The transported trivialization of the unit pair at `f`, with the two fields of the pair read
off: the trivialization of the unit pair is the canonical trivialization of the tensor powers of
the structure sheaf of `S` followed by multiplication by `f`. -/
private theorem basePairTriv_unitPair (f : (Scheme.Γ.obj (op S))ˣ) :
    basePairTriv B S hS τ n (unitPair S n f) =
      ((powerTransportIso S.presheaf (ringSheafCond S)
            (BigFppfOver.baseRingedSite B S hS τ).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2
            (BigFppfOver.baseAssociatedModule B S hS τ)
            (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ)
            (BigFppfOver.baseAssociatedModuleTensorIso' B S hS τ)
            (SheafOfModules.unit (ringSheaf S)) n).symm ≪≫
          (BigFppfOver.baseAssociatedModule B S hS τ).mapIso
            (structureSheafTensorPowerIso S n ≪≫
              scalarIso S f (SheafOfModules.unit (ringSheaf S)))) ≪≫
        BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ :=
  rfl

omit [∀ σ : SiteKind, HasSheafify (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u}]
  [∀ σ : SiteKind,
    HasExt.{u} (Sheaf (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u})] in
/-- The same at `f = 1`, where the trivialization of the unit pair is the canonical one by
`AlgebraicGeometry.unitPair_one_trivialization`. -/
private theorem basePairTriv_unitPair_one :
    ((powerTransportIso S.presheaf (ringSheafCond S)
            (BigFppfOver.baseRingedSite B S hS τ).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O).2
            (BigFppfOver.baseAssociatedModule B S hS τ)
            (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ)
            (BigFppfOver.baseAssociatedModuleTensorIso' B S hS τ)
            (SheafOfModules.unit (ringSheaf S)) n).symm ≪≫
          (BigFppfOver.baseAssociatedModule B S hS τ).mapIso
            (structureSheafTensorPowerIso S n)) ≪≫
        BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ =
      basePairTriv B S hS τ n (unitPair S n 1) := by
  rw [← unitPair_one_trivialization S n]; rfl

omit [∀ σ : SiteKind, HasSheafify (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u}]
  [∀ σ : SiteKind,
    HasExt.{u} (Sheaf (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u})] in
/-- The functor carries the canonical trivialization followed by multiplication by `f` to the
image of the canonical trivialization followed by the image of multiplication by `f`. -/
private theorem mapIso_structureSheafTensorPowerIso_trans_scalarIso
    (f : (Scheme.Γ.obj (op S))ˣ) :
    (BigFppfOver.baseAssociatedModule B S hS τ).mapIso
        (structureSheafTensorPowerIso S n ≪≫
          scalarIso S f (SheafOfModules.unit (ringSheaf S))) =
      (BigFppfOver.baseAssociatedModule B S hS τ).mapIso (structureSheafTensorPowerIso S n) ≪≫
        (BigFppfOver.baseAssociatedModule B S hS τ).mapIso
          (scalarIso S f (SheafOfModules.unit (ringSheaf S))) :=
  Functor.mapIso_trans _ _ _

omit [∀ σ : SiteKind, HasSheafify (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u}]
  [∀ σ : SiteKind,
    HasExt.{u} (Sheaf (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u})] in
/-- **The comparison of the two structure sheaves carries the associated module of multiplication
by a global unit of `S` to multiplication by that unit over the terminal object of the big
`τ`-site.**  This is `AlgebraicGeometry.baseAssociatedModule_map_scalarEnd` followed by
`AlgebraicGeometry.scalarEndOfTerminal_naturality`. -/
private theorem mapIso_scalarIso_trans_baseAssociatedModuleUnitIso
    (hT : IsTerminal (C := BigFppfOver B S hS) (Over.mk (𝟙 (B.obj hS))))
    (f : (Scheme.Γ.obj (op S))ˣ) :
    (BigFppfOver.baseAssociatedModule B S hS τ).mapIso
          (scalarIso S f (SheafOfModules.unit (ringSheaf S))) ≪≫
        BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ =
      BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ ≪≫
        scalarIsoOfTerminal (BigFppfOver.baseRingedSite B S hS τ) hT f
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O)) :=
  Iso.ext ((congrArg (fun z => z ≫ (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ).hom)
      (baseAssociatedModule_map_scalarEnd B S hS τ hT f.val
        (SheafOfModules.unit (ringSheaf S)))).trans
    (scalarEndOfTerminal_naturality (BigFppfOver.baseRingedSite B S hS τ) hT f.val
      (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ).hom))

omit [∀ σ : SiteKind, HasSheafify (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u}]
  [∀ σ : SiteKind,
    HasExt.{u} (Sheaf (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u})] in
/-- **The transported trivialization of the unit pair at `f` is the transported trivialization of
the unit pair at `1`, twisted by `f`** over the terminal object of the big `τ`-site. -/
private theorem basePairTriv_unitPair_eq
    (hT : IsTerminal (C := BigFppfOver B S hS) (Over.mk (𝟙 (B.obj hS))))
    (f : (Scheme.Γ.obj (op S))ˣ) :
    basePairTriv B S hS τ n (unitPair S n f) =
      basePairTriv B S hS τ n (unitPair S n 1) ≪≫
        scalarIsoOfTerminal (BigFppfOver.baseRingedSite B S hS τ) hT f
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O)) := by
  rw [basePairTriv_unitPair, mapIso_structureSheafTensorPowerIso_trans_scalarIso,
    ← basePairTriv_unitPair_one]
  exact trans_trans_comm _ _ _ _ _
    (mapIso_scalarIso_trans_baseAssociatedModuleUnitIso B S hS τ hT f)

omit [∀ σ : SiteKind, HasSheafify (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u}]
  [∀ σ : SiteKind,
    HasExt.{u} (Sheaf (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u})] in
/-- The site-level trivialization of the unit pair at a product, with the second factor split
off, by `AlgebraicGeometry.scalarIsoOfTerminal_trans`. -/
private theorem powerMap_trans_unitPairTrivialization_mul
    (hT : IsTerminal (C := BigFppfOver B S hS) (Over.mk (𝟙 (B.obj hS))))
    (c f : (Scheme.Γ.obj (op S))ˣ) :
    powerMap (BigFppfOver.baseRingedSite B S hS τ)
          (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ) n ≪≫
        unitPairTrivialization (BigFppfOver.baseRingedSite B S hS τ) hT n (c * f) =
      powerMap (BigFppfOver.baseRingedSite B S hS τ)
            (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ) n ≪≫
          unitPowerTrivialization (BigFppfOver.baseRingedSite B S hS τ) hT n ≪≫
            scalarIsoOfTerminal (BigFppfOver.baseRingedSite B S hS τ) hT c
                (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
                    (BigFppfOver.baseRingedSite B S hS τ).O)) ≪≫
              scalarIsoOfTerminal (BigFppfOver.baseRingedSite B S hS τ) hT f
                (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
                    (BigFppfOver.baseRingedSite B S hS τ).O)) :=
  congrArg
    (fun z => powerMap (BigFppfOver.baseRingedSite B S hS τ)
          (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ) n ≪≫
        unitPowerTrivialization (BigFppfOver.baseRingedSite B S hS τ) hT n ≪≫ z)
    (scalarIsoOfTerminal_trans (BigFppfOver.baseRingedSite B S hS τ) hT c f
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfOver.baseRingedSite B S hS τ).O))).symm

omit [∀ σ : SiteKind, HasSheafify (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u}]
  [∀ σ : SiteKind,
    HasExt.{u} (Sheaf (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u})] in
/-- **The transported trivialization of the unit pair is the site-level trivialization of the
unit pair, after one fixed twist.**  There is a global unit `c` of `S`, independent of `f`, with
`AlgebraicGeometry.basePairTriv` at the unit pair of `f` the comparison of the two structure
sheaves followed by
`Stacks.Cohomology.Torsors.Generators.unitPairTrivialization` at `c * f`.

This is the identification the compatibility of the comparison map of Tag 040Q with the left-hand
end of the two extensions was missing. -/
@[stacks 040Q "the transported trivialization of the unit pair of a global unit f is the \
site-level trivialization of the unit pair at c * f, for one global unit c independent of f; \
this is the identification the compatibility of the comparison map with the left-hand end of the \
two extensions needs, and that compatibility is proved below, not here"]
public theorem exists_unitPairTrivialization_eq_basePairTriv
    (hT : IsTerminal (C := BigFppfOver B S hS) (Over.mk (𝟙 (B.obj hS)))) :
    ∃ c : (Scheme.Γ.obj (op S))ˣ, ∀ f : (Scheme.Γ.obj (op S))ˣ,
      powerMap (BigFppfOver.baseRingedSite B S hS τ)
            (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ) n ≪≫
          unitPairTrivialization (BigFppfOver.baseRingedSite B S hS τ) hT n (c * f) =
        basePairTriv B S hS τ n (unitPair S n f) := by
  obtain ⟨c, hc⟩ := exists_scalarIsoOfTerminal (BigFppfOver.baseRingedSite B S hS τ) hT
    ((powerMap (BigFppfOver.baseRingedSite B S hS τ)
          (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ) n ≪≫
        unitPowerTrivialization (BigFppfOver.baseRingedSite B S hS τ) hT n).symm ≪≫
      basePairTriv B S hS τ n (unitPair S n 1))
  refine ⟨c, fun f => ?_⟩
  refine (powerMap_trans_unitPairTrivialization_mul B S hS τ n hT c f).trans ?_
  refine (trans_trans_cancel _ _ _ _ _ hc).trans ?_
  exact (basePairTriv_unitPair_eq B S hS τ n hT f).symm

/-! ### The compatibility with the left-hand end -/

/-- The comparison map at the class of the unit pair of `f`, read through the twist `c`: it is
minus the Kummer boundary of `c * f`.

This is `AlgebraicGeometry.trivializationTorsor_class_eq_of_iso'` at the comparison of the two
structure sheaves, fed the identification above, followed by
`AlgebraicGeometry.torsorIsoClassesEquivH1_trivializationTorsor_unitPair_eq_neg`. -/
private theorem basePairCohomologyClass_unitPair_mul
    (hroot : LocalRoots (BigFppfOver.baseRingedSite B S hS τ) n)
    (hSE : (kummerSequence (BigFppfOver.baseOverTopology B S hS τ)
      (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n).ShortExact)
    (hT : IsTerminal (C := BigFppfOver B S hS) (Over.mk (𝟙 (B.obj hS))))
    (c : (Scheme.Γ.obj (op S))ˣ)
    (hc : ∀ f : (Scheme.Γ.obj (op S))ˣ,
      powerMap (BigFppfOver.baseRingedSite B S hS τ)
            (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ) n ≪≫
          unitPairTrivialization (BigFppfOver.baseRingedSite B S hS τ) hT n (c * f) =
        basePairTriv B S hS τ n (unitPair S n f))
    (f : (Scheme.Γ.obj (op S))ˣ) :
    basePairCohomologyClassHom B S hS τ n hroot (pairClass (unitPair S n f)) =
      -kummerBoundary (BigFppfOver.baseOverTopology B S hS τ) (BigFppfOver.toScheme B S hS)
        (unitsPresheaf_isSheaf_base B S hS τ) n hSE hT (c * f) := by
  refine Eq.trans (congrArg (torsorIsoClassesEquivH1 _) (trivializationTorsor_class_eq_of_iso'
    (BigFppfOver.baseOverTopology B S hS τ) (BigFppfOver.toScheme B S hS)
    (BigFppfOver.baseRingedSite B S hS τ).O.property (unitsPresheaf_isSheaf_base B S hS τ) n
    (baseRingedSite_isLocallyRinged B S hS τ) hroot _ _
    (basePairSheaf_isInvertible B S hS τ n (unitPair S n f))
    (isInvertible_unit_ringSheaf (BigFppfOver.baseRingedSite B S hS τ)) _ _
    (BigFppfOver.baseAssociatedModulePicardUnitIso B S hS τ) (hc f))) ?_
  exact torsorIsoClassesEquivH1_trivializationTorsor_unitPair_eq_neg
    (BigFppfOver.baseOverTopology B S hS τ) (BigFppfOver.toScheme B S hS)
    (BigFppfOver.baseRingedSite B S hS τ).O.property (unitsPresheaf_isSheaf_base B S hS τ) n
    (baseRingedSite_isLocallyRinged B S hS τ) hroot hSE hT (c * f)

/-- **The comparison map of Tag 040Q is compatible with the left-hand end of the two
extensions**: it carries the class of the pair `(𝒪_S, f)` of a global unit `f` to minus the
Kummer boundary of `f`.

The twist `c` of the identification above is killed by reading the statement at `f = 1`: the
class of the unit pair at `1` is the zero class of pairs and the comparison is a homomorphism, so
the Kummer boundary of `c` vanishes, and the Kummer boundary is a homomorphism by
`AlgebraicGeometry.kummerBoundary_mul`.

This is the hypothesis `hci` of `Stacks.Kummer.bijective_of_comparison`.

Tag 040Q itself is registered on `AlgebraicGeometry.pairClassesAddEquivH1Etale` and its fppf and
syntomic companions. -/
public theorem basePairCohomologyClass_unitPair
    (hroot : LocalRoots (BigFppfOver.baseRingedSite B S hS τ) n)
    (hSE : (kummerSequence (BigFppfOver.baseOverTopology B S hS τ)
      (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n).ShortExact)
    (hT : IsTerminal (C := BigFppfOver B S hS) (Over.mk (𝟙 (B.obj hS))))
    (f : (Scheme.Γ.obj (op S))ˣ) :
    basePairCohomologyClassHom B S hS τ n hroot (pairClass (unitPair S n f)) =
      -kummerBoundary (BigFppfOver.baseOverTopology B S hS τ) (BigFppfOver.toScheme B S hS)
        (unitsPresheaf_isSheaf_base B S hS τ) n hSE hT f := by
  obtain ⟨c, hc⟩ := exists_unitPairTrivialization_eq_basePairTriv B S hS τ n hT
  have hpair : pairClass (unitPair S n 1) = (0 : PairClasses S n) :=
    (unitPairHom S n).map_zero
  have hzero : kummerBoundary (BigFppfOver.baseOverTopology B S hS τ)
      (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n hSE hT c = 0 := by
    have h1 := basePairCohomologyClass_unitPair_mul B S hS τ n hroot hSE hT c hc 1
    rw [mul_one, hpair, map_zero] at h1
    exact neg_eq_zero.1 h1.symm
  have h2 := basePairCohomologyClass_unitPair_mul B S hS τ n hroot hSE hT c hc f
  rwa [kummerBoundary_mul (BigFppfOver.baseOverTopology B S hS τ) (BigFppfOver.toScheme B S hS)
    (unitsPresheaf_isSheaf_base B S hS τ) n hSE hT c f, hzero, zero_add] at h2

end AlgebraicGeometry

end
