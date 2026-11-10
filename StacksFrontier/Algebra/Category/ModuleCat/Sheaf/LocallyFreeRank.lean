module

import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Topology.Sheaves.Module

public import StacksFrontier.Topology.Sheaves.Stalk.ValuedInCategory
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description (Stacks Tag 01C9)

Let `(X, O_X)` be a ringed space, i.e. a topological space `X` together with a sheaf of
*commutative* unital rings `O_X`.  For a point `x : X` write `O_{X,x}` for the stalk of
`O_X` at `x`.

* (Locally free sheaf of modules.)  A sheaf `F` of `O_X`-modules is *locally free* if
  every point `x : X` has an open neighbourhood `U`, an index set `I` and an isomorphism
  of `O_X|_U`-modules
    `F|_U ≅ ⊕_{i ∈ I} O_X|_U`,
  where `⊕_{i ∈ I} O_X|_U` denotes the direct sum (coproduct) of `I` copies of the
  structure sheaf restricted to `U`.

* (Locally constant function.)  A function `f : X → S` is *locally constant* if every
  point has an open neighbourhood on which `f` is constant.

* (Support of `O_X` is `X`.)  This means that for every `x : X` the stalk `O_{X,x}` is a
  nonzero ring, equivalently `Nontrivial O_{X,x}` (i.e. `1 ≠ 0`).

## Theorem (Stacks Tag 01C9)

Let `(X, O_X)` be a ringed space such that the support of `O_X` is all of `X`, i.e.
every stalk `O_{X,x}` is a nonzero ring.  Let `F` be a locally free sheaf of
`O_X`-modules.  Then there exists a locally constant function

  `rank_F : X → {0, 1, 2, …} ∪ {∞}`

with the following property: for every point `x : X` and every index set `I` such that
`F` is isomorphic to `⊕_{i ∈ I} O_X|_U` on some open neighbourhood `U` of `x`, the
cardinality of `I` equals `rank_F x`.

This asserts simultaneously:
1. (Well-definedness of the rank at each point.)  The cardinality `|I|` is independent of
   the chosen neighbourhood `U ∋ x` and the chosen trivialisation; this common cardinality
   is `rank_F x`.
2. (Local constancy.)  The function `x ↦ rank_F x` is locally constant on `X`.

The codomain `{0, 1, 2, …} ∪ {∞}` is read as the collection of possible cardinalities of
index sets.  Finite index sets give natural numbers; infinite index sets give infinite
cardinals.  Following the problem statement (which explicitly allows tracking the
cardinalities exactly), we use the type `Cardinal` as the codomain of the rank function:
the symbol `∞` of the informal statement corresponds to an infinite cardinal, and
`rank_F x` records the cardinality `|I|` exactly.  The role of the nonvanishing hypothesis
on the stalks is that over a nonzero commutative ring `R = O_{X,x}` the free module rank is
invariant (invariant basis number): `R^{(I)} ≅ R^{(J)}` implies `|I| = |J|`; without it the
zero ring would make every `R^{(I)}` trivial, breaking well-definedness.

## Formalisation notes

* The structure sheaf `O_X` is modelled as a sheaf of *commutative* unital rings, i.e. a
  term `O : Sheaf (Opens.grothendieckTopology X) CommRingCat`.  Mathlib's `SheafOfModules`
  is taken over a sheaf of (possibly non-commutative) rings, so we transport `O` along the
  forgetful functor `CommRingCat ⥤ RingCat` to obtain the base sheaf of rings `R := O_X`
  over which `F` is a sheaf of modules; commutativity is genuinely recorded by `O`.

* The restriction `F|_U` (resp. `O_X|_U`) of a sheaf of modules (resp. ring sheaf) to an
  open set `U` is the genuine pullback along the open immersion `U ↪ X`, formalised as the
  `SheafOfModules.pushforward`/`sheafPushforwardContinuous` along the open-inclusion functor
  `Opens U ⥤ Opens X` (`restrictMod`/`restrictRing` below).  This carries the inherited
  `O_X|_U`-module structure.

* The direct sum `⊕_{i ∈ I} O_X|_U` is the genuine categorical coproduct of `I` copies of
  the structure sheaf inside the category of sheaves of modules over `O_X|_U`, namely the
  free sheaf of modules `SheafOfModules.free I` (whose universal property identifies it with
  the coproduct of `I` copies of the unit `O_X|_U`).

* A trivialisation `F|_U ≅ ⊕_{i ∈ I} O_X|_U` is therefore a single isomorphism in the
  category `SheafOfModules (O_X|_U)` between the genuine restriction `restrictMod F` and the
  free sheaf of modules `SheafOfModules.free I`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace CategoryTheory.Limits

universe u

namespace LocallyFreeRank

-- ## Restriction to an open subset

/-- The open-inclusion functor `Opens U ⥤ Opens X` induced by the open embedding of the
subspace `U` into `X`.  It sends an open subset of `U` to its image, an open subset of
`X`. -/
noncomputable def inclF (X : TopCat.{u}) (U : Opens X) : Opens U ⥤ Opens X :=
  IsOpenMap.functor (f := U.inclusion') (U.isOpenEmbedding'.isOpenMap)

/-- The open-inclusion functor `inclF X U` is faithful. -/
instance instFaithful (X : TopCat.{u}) (U : Opens X) : (inclF X U).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- The open-inclusion functor `inclF X U` is full. -/
instance instFull (X : TopCat.{u}) (U : Opens X) : (inclF X U).Full where
  map_surjective {V₁ V₂} f := by
    refine ⟨homOfLE ?_, Subsingleton.elim _ _⟩
    intro x hx
    have hmem : (x : X) ∈ ((inclF X U).obj V₂ : Opens X) := leOfHom f ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyeq⟩ := hmem
    rwa [Subtype.val_injective hyeq] at hy

/-- The open-inclusion functor is downwards closed: any open `d ⊆ X` lying under the image
of an open of `U` is itself contained in `U`, hence is the image of an open of `U`. -/
noncomputable def downClosed (X : TopCat.{u}) (U : Opens X) :
    {c : Opens U} → {d : Opens X} → (d ⟶ (inclF X U).obj c) →
      (c' : Opens U) × ((inclF X U).obj c' ≅ d) :=
  fun {c} {d} f => by
    have hdU : (d : Set X) ⊆ (U : Set X) := fun x hx => by
      obtain ⟨y, _, rfl⟩ := leOfHom f hx; exact y.2
    refine ⟨⟨Subtype.val ⁻¹' (d : Set X), d.2.preimage continuous_subtype_val⟩, eqToIso ?_⟩
    apply Opens.ext; ext x
    simp only [inclF, IsOpenMap.functor]
    exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨⟨x, hdU hx⟩, hx, rfl⟩⟩

/-- The open-inclusion functor `inclF X U` sends covering sieves of `U` to covering sieves
of `X`. -/
lemma instCoverPreserving (X : TopCat.{u}) (U : Opens X) :
    CoverPreserving (Opens.grothendieckTopology U) (Opens.grothendieckTopology X) (inclF X U) := by
  constructor
  intro V S hS x hx
  obtain ⟨y, hyV, rfl⟩ := hx
  obtain ⟨W, f, hf, hyW⟩ := hS y hyV
  exact ⟨(inclF X U).obj W, (inclF X U).map f,
    Sieve.image_mem_functorPushforward (inclF X U) S hf, ⟨y, hyW, rfl⟩⟩

/-- The open-inclusion functor `inclF X U` is continuous for the Grothendieck topologies
of open covers on `U` and on `X`. -/
@[sga "4 III 1.9.2", sga "4 III 2.7" "continuity of Φ"]
instance instContinuous (X : TopCat.{u}) (U : Opens X) :
    (inclF X U).IsContinuous (Opens.grothendieckTopology U) (Opens.grothendieckTopology X) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfDownwardsClosed _ _ (downClosed X U)) (instCoverPreserving X U)

/-- The restriction `R|_U` of a sheaf of rings `R` on `X` to an open subset `U`, obtained
as the pullback along the open immersion `U ↪ X` (`sheafPushforwardContinuous` of the
open-inclusion functor).  This is the genuine `O_X|_U`. -/
@[ega "IV 21.13.3", sga "4 IV 14.1" "partial"]
noncomputable def restrictRing (X : TopCat.{u}) (U : Opens X)
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    Sheaf (Opens.grothendieckTopology U) RingCat.{u} :=
  ((inclF X U).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)).obj R

/-- The restriction `F|_U` of a sheaf of `O_X`-modules `F` to an open subset `U`, with its
inherited `O_X|_U`-module structure.  It is the genuine pullback of `F` along the open
immersion `U ↪ X`, formalised as `SheafOfModules.pushforward` along the open-inclusion
functor over the identity morphism of the restricted ring sheaf `O_X|_U`. -/
@[ega "0 3.1.5", ega "IV 21.13.3", sga "4 IV 11.2.2" "special case"]
noncomputable def restrictMod (X : TopCat.{u}) (U : Opens X)
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (F : SheafOfModules.{u} R) :
    SheafOfModules.{u} (restrictRing X U R) :=
  (SheafOfModules.pushforward
    (J := Opens.grothendieckTopology U) (K := Opens.grothendieckTopology X)
    (F := inclF X U) (𝟙 (restrictRing X U R))).obj F

/-- **The two ways of restricting a sheaf of modules to an open `U` agree on the nose.**
Mathlib's equivalence `TopologicalSpace.Opens.sheafOfModulesEquivOver` between sheaves of modules
on the slice site over `U` and sheaves of modules on the space `U` carries the slice restriction
`F.over U` to the genuine restriction `restrictMod X U R F`, and it does so definitionally: both
are `SheafOfModules.pushforward` along the open-inclusion functor `V ↦ V` of `Opens U ⥤ Opens X`
over the identity of the restricted sheaf of rings.

Naming the identification is what lets a trivialisation be produced from local-generator data:
`SheafOfModules.LocalGeneratorsData` is stated on the slice site, `Trivialization` on the space
`U`, and this is the only step between them. -/
noncomputable def restrictModIsoOver (X : TopCat.{u}) (U : Opens X)
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (F : SheafOfModules.{u} R) :
    (U.sheafOfModulesEquivOver R).functor.obj (F.over U) ≅ restrictMod X U R F :=
  Iso.refl _

-- ## Main Definition(s)

/-- A *trivialisation* of a sheaf of `O_X`-modules `F` on an open set `U`: an index set `I`
together with an isomorphism, in the category of sheaves of `O_X|_U`-modules,
`F|_U ≅ ⊕_{i ∈ I} O_X|_U`, where `⊕_{i ∈ I} O_X|_U = SheafOfModules.free I` is the
categorical coproduct of `I` copies of the (restricted) structure sheaf.  Here `F|_U` is the
genuine restriction `restrictMod F` carrying the inherited `O_X|_U`-module structure. -/
structure Trivialization (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (F : SheafOfModules.{u} R) (U : Opens X) where
  /-- The index set of the free sheaf. -/
  ι : Type u
  /-- The trivialising isomorphism `F|_U ≅ ⊕_{i ∈ ι} O_X|_U` of sheaves of modules over the
  restricted structure sheaf `O_X|_U`. -/
  iso : restrictMod X U R F ≅ SheafOfModules.free.{u} ι

/-- A sheaf of `O_X`-modules `F` is *locally free* if every point `x : X` admits an open
neighbourhood `U` on which `F` is trivial, i.e. `F|_U ≅ ⊕_{i ∈ I} O_X|_U` for some index
set `I`. -/
@[ega "0 5.4.1", ega "II 6.5.1" "(I)", ega "IV 18.2.7" "partial", ega "IV 21.5.3" "partial"]
def IsLocallyFree (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (F : SheafOfModules.{u} R) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧ Nonempty (Trivialization X R F U)

/-- The cardinality of the index set of a trivialisation. -/
noncomputable def Trivialization.rank {X : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    {F : SheafOfModules.{u} R} {U : Opens X}
    (t : Trivialization X R F U) : Cardinal.{u} :=
  Cardinal.mk t.ι

/-- The base sheaf of (possibly non-commutative) rings underlying a structure sheaf of
*commutative* rings `O`, obtained by composing with the forgetful functor
`CommRingCat ⥤ RingCat`.  Sheaves of modules over `O_X` are taken over this base. -/
noncomputable def toRingSheaf (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj O

/-- The hypothesis that the support of `O_X` is all of `X`: every stalk `O_{X,x}` is a
nonzero ring. -/
def StalksNontrivial (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) : Prop :=
  ∀ x : X, Nontrivial (ToType (TopCat.Presheaf.stalk (X := X) O.obj x))

-- ## Stalk-of-morphism infrastructure (verified)

/-- From a morphism `f : M ⟶ N` of presheaves of modules over a sheaf of rings `R`, the
induced map on stalks at `x` is `R.stalk x`-linear. -/
@[ega "0 3.1.6" "special case", ega "0 4.4.3" "special case"]
noncomputable def stalkLMap {X : TopCat.{u}} {R : TopCat.Presheaf RingCat.{u} X}
    {M N : PresheafOfModules.{u} R} (f : M ⟶ N) (x : X) :
    ToType (TopCat.Presheaf.stalk M.presheaf x) →ₗ[ToType (R.stalk x)]
      ToType (TopCat.Presheaf.stalk N.presheaf x) where
  toFun := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((PresheafOfModules.toPresheaf
      R).map f)
  map_add' a b := map_add _ a b
  map_smul' r m := by
    dsimp
    obtain ⟨U, hxU, m₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
    obtain ⟨V, hxV, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
    set W : Opens X := U ⊓ V with hW
    have hxW : x ∈ W := ⟨hxU, hxV⟩
    have hr : (ConcreteCategory.hom (R.germ V x hxV)) r₀
        = (ConcreteCategory.hom (R.germ W x hxW))
            ((ConcreteCategory.hom (R.map (homOfLE (inf_le_right)).op)) r₀) := by
      rw [TopCat.Presheaf.germ_res_apply]
    have hm : (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf U x hxU)) m₀
        = (ConcreteCategory.hom (TopCat.Presheaf.germ M.presheaf W x hxW))
            ((ConcreteCategory.hom (M.presheaf.map (homOfLE (inf_le_left)).op)) m₀) := by
      rw [TopCat.Presheaf.germ_res_apply]
    rw [hr, hm]
    set rr : ToType (R.obj (Opposite.op W)) := (ConcreteCategory.hom (R.map (homOfLE
        (inf_le_right)).op)) r₀ with hrr
    set mm : ToType (M.presheaf.obj (Opposite.op W)) := (ConcreteCategory.hom (M.presheaf.map
        (homOfLE (inf_le_left)).op)) m₀ with hmm
    rw [← PresheafOfModules.germ_ringCat_smul]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW ((PresheafOfModules.toPresheaf R).map
        f) (rr • mm)]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW ((PresheafOfModules.toPresheaf R).map
        f) mm]
    erw [← PresheafOfModules.germ_ringCat_smul N x W hxW rr ((ConcreteCategory.hom
        (((PresheafOfModules.toPresheaf R).map f).app (Opposite.op W))) mm)]
    congr 1
    exact (f.app (Opposite.op W)).hom.map_smul rr mm

/-- From an isomorphism `e : M ≅ N` of presheaves of modules over a sheaf of rings `R`, the
induced `R.stalk x`-linear equivalence of stalks at `x`. -/
noncomputable def stalkLEquivOfIso {X : TopCat.{u}} {R : TopCat.Presheaf RingCat.{u} X}
    {M N : PresheafOfModules.{u} R} (e : M ≅ N) (x : X) :
    ToType (TopCat.Presheaf.stalk M.presheaf x) ≃ₗ[ToType (R.stalk x)]
      ToType (TopCat.Presheaf.stalk N.presheaf x) := by
  set EE := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      ((PresheafOfModules.toPresheaf R).mapIso e) with hEE
  refine LinearEquiv.ofLinearMap (stalkLMap e.hom x) (stalkLMap e.inv x) ?_ ?_
  · ext z
    change (ConcreteCategory.hom EE.hom) ((ConcreteCategory.hom EE.inv) z) = z
    exact EE.inv_hom_id_apply z
  · ext z
    change (ConcreteCategory.hom EE.inv) ((ConcreteCategory.hom EE.hom) z) = z
    exact EE.hom_inv_id_apply z

-- ## Key sub-lemmas towards Stacks Tag 01C9

/-
## Proof outline (informal, rigorous)

We use the codomain `Cardinal` and define, for each `x : X`,
`rankF x := Cardinal.mk t.ι` for *some* trivialisation `t` on *some* open neighbourhood of
`x` (which exists by `hF`).  The whole content of the theorem then reduces to the single
algebraic fact `Trivialization.rank_eq_of_mem` below: any two trivialisations whose open
domains both contain `x` have the same rank.  Indeed:

* Well-definedness of the matching property `t.rank = rankF x` is *exactly* an instance of
  `rank_eq_of_mem` (compare an arbitrary `t` with the chosen trivialisation `t_x`).
* Local constancy: if `t_x` is the chosen trivialisation on `U_x ∋ x` then for every `y ∈ U_x`
  the restriction of `t_x` to a neighbourhood of `y` is again a trivialisation containing `y`,
  so `rankF y = rank(t_x) = rankF x`; hence `rankF` is constant on the open `U_x ∋ x`.

The crux `rank_eq_of_mem` is the standard "pass to the stalk + invariant basis number"
argument:

1. A trivialisation `t : F|_U ≅ ⊕_{i∈t.ι} O_X|_U` induces, by applying the stalk functor at
   `x ∈ U`, an isomorphism of `O_{X,x}`-modules `F_x ≅ (t.ι →₀ O_{X,x})`.  (The stalk of the
   restriction `F|_U` at `x ∈ U` is the stalk `F_x` since restriction is along an open
   immersion, an inducing map; and the stalk of the free sheaf `⊕_{i∈I} O_X|_U` is the free
   module `(I →₀ O_{X,x})` because the stalk functor `= colim` preserves the coproduct.)
2. Given two trivialisations `t` (on `U ∋ x`) and `s` (on `V ∋ x`), composing the two stalk
   isomorphisms gives a linear equivalence `(t.ι →₀ O_{X,x}) ≃ₗ[O_{X,x}] (s.ι →₀ O_{X,x})`.
3. Since `O_{X,x}` is a *nonzero* commutative ring (`hO`), it has `StrongRankCondition`
   (`commRing_strongRankCondition`), so taking `Module.rank` of both sides and using
   `rank_finsupp_self` yields `Cardinal.mk t.ι = Cardinal.mk s.ι`, i.e. `t.rank = s.rank`.
-/

/-- The `O_{X,x}`-module structure on the stalk `F_x` of a sheaf of `O_X`-modules at a
point `x`, where `O` is a sheaf of *commutative* rings.  This is Mathlib's
`PresheafOfModules` stalk-module instance, applied through the definitional equality
`(toRingSheaf X O).val = O.val ⋙ forget₂ CommRingCat RingCat` (instance search does not fire
through the `toRingSheaf`/`sheafCompose` wrapper, so we name it). -/
noncomputable instance instModuleStalkF
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (F : SheafOfModules.{u} (toRingSheaf X O)) (x : X) :
    Module (ToType (TopCat.Presheaf.stalk O.obj x))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x

/-- Abbreviation for the *restricted* ring stalk `kU := (O_X|_U)_{⟨x,hU⟩}`, the natural base
ring over which the stalks of `restrictMod`/`SheafOfModules.free` at `⟨x,hU⟩ : ↥U` are
modules.  (The point lives in the subspace `↥U`, taken as `TopCat.of (U : Type u)`.) -/
noncomputable abbrev restrictStalkRing
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) (U : Opens X) (hU : x ∈ U) : Type u :=
  ToType (@TopCat.Presheaf.stalk RingCat.{u} _ _ (TopCat.of (U : Type u))
    ((restrictRing X U (toRingSheaf X O)).obj) (⟨x, hU⟩ : (U : Type u)))

/-- The `kU := restrictStalkRing`-module structure on the stalk of the restriction
`restrictMod X U R F` at `⟨x,hU⟩ : ↥U`.  This is Mathlib's `PresheafOfModules` stalk-module
instance for the `PresheafOfModules ((restrictRing …).val)` underlying `restrictMod`, named
so that instance search fires with the base ring written literally as `restrictStalkRing`. -/
noncomputable instance instModuleStalkRestrictMod
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (F : SheafOfModules.{u} (toRingSheaf X O))
    (x : X) (U : Opens X) (hU : x ∈ U) :
    Module (restrictStalkRing X O x U hU)
      (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((restrictMod X U (toRingSheaf X O) F).val.presheaf)
          (⟨x, hU⟩ : (U : Type u)))) :=
  PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier
    (X := TopCat.of (U : Type u))
    (R := (restrictRing X U (toRingSheaf X O)).obj)
    (restrictMod X U (toRingSheaf X O) F).val
    (⟨x, hU⟩ : (U : Type u))

/-- The `kU := restrictStalkRing`-module structure on the stalk of the free sheaf
`SheafOfModules.free ι` over the restricted ring sheaf, at `⟨x,hU⟩ : ↥U`.  Named (analogously
to `instModuleStalkRestrictMod`) so that instance search fires with the base ring written
literally as `restrictStalkRing`. -/
noncomputable instance instModuleStalkFree
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) (U : Opens X) (hU : x ∈ U) (ι : Type u) :
    Module (restrictStalkRing X O x U hU)
      (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((SheafOfModules.free.{u} (R := restrictRing X U (toRingSheaf X O)) ι).val.presheaf)
          (⟨x, hU⟩ : (U : Type u)))) :=
  PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier
    (X := TopCat.of (U : Type u))
    (R := (restrictRing X U (toRingSheaf X O)).obj)
    (SheafOfModules.free.{u} (R := restrictRing X U (toRingSheaf X O)) ι).val
    (⟨x, hU⟩ : (U : Type u))

/-- The `kU := restrictStalkRing`-module structure on the stalk of the unit sheaf
`SheafOfModules.unit (restrictRing X U (toRingSheaf X O))`, at `⟨x,hU⟩ : ↥U`.  Named (analogously
to `instModuleStalkFree`) so that instance search fires with the base ring written literally
as `restrictStalkRing`. -/
noncomputable instance instModuleStalkUnit
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) (U : Opens X) (hU : x ∈ U) :
    Module (restrictStalkRing X O x U hU)
      (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val.presheaf)
          (⟨x, hU⟩ : (U : Type u)))) :=
  PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier
    (X := TopCat.of (U : Type u))
    (R := (restrictRing X U (toRingSheaf X O)).obj)
    (SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val
    (⟨x, hU⟩ : (U : Type u))

/-- **(Sub-lemma (ring): reconciliation of the restricted ring stalk with the ambient stalk.)**
The stalk of the *restricted* structure sheaf `O_X|_U` at `⟨x,hU⟩ : ↥U` is ring-isomorphic to
the ambient stalk `O_{X,x}`.

PROOF (cofinality; no off-the-shelf iso — `stalkPushforward_iso_of_isInducing` does NOT
exist).  `restrictRing` is the *site* pushforward `sheafPushforwardContinuous` along
`inclF X U = IsOpenMap.functor (U.isOpenEmbedding'.isOpenMap)`.  The stalk at `⟨x,hU⟩` is
`colimit ((OpenNhds.inclusion ⟨x,hU⟩).op ⋙ —)`.  Via `IsOpenMap.adjunctionNhds ⟨x,hU⟩`
(`functorNhds ⟨x,hU⟩ ⊣ OpenNhds.map …`) the functor `functorNhds ⟨x,hU⟩` is `Initial`
(`Functor.initial_of_adjunction`), its `.op` is `Final` (`Functor.final_op_of_initial`), and
`Functor.Final.colimitIso` gives `(restrictRing …).val.stalk ⟨x,hU⟩ ≅ O.val.stalk x` (gluing
the neighbourhood diagrams with `OpenNhds.inclusionMapIso`); take the underlying `RingEquiv`. -/
theorem Trivialization.stalk_restrictRing_ringEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) {U : Opens X} (hU : x ∈ U) :
    Nonempty (restrictStalkRing X O x U hU ≃+* ToType (TopCat.Presheaf.stalk O.obj x)) := by
  -- Core cofinality iso (in RingCat) for the ring sheaf `R := toRingSheaf X O`:
  -- the stalk of the open-immersion pushforward `restrictRing` at `⟨x,hU⟩` is isomorphic to
  -- the ambient stalk of `R` at `x`.  Build it directly via `Functor.Final.colimitIso`:
  -- `restrictRing` is precomposition with `(inclF X U).op`, and
  -- `OpenNhds.inclusion ⟨x,hU⟩ ⋙ inclF X U = (functorNhds ⟨x,hU⟩) ⋙ OpenNhds.inclusion x`
  -- definitionally; `functorNhds ⟨x,hU⟩` is initial (adjunction), so its `.op` is final.
  have coreIso :
      (@TopCat.Presheaf.stalk RingCat.{u} _ _ (TopCat.of (U : Type u))
        ((restrictRing X U (toRingSheaf X O)).obj) (⟨x, hU⟩ : (U : Type u)))
        ≅ TopCat.Presheaf.stalk (toRingSheaf X O).obj x := by
    have h : IsOpenMap (ConcreteCategory.hom (U.inclusion')) := U.isOpenEmbedding'.isOpenMap
    have hinit : (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).Initial :=
      Functor.initial_of_adjunction (h.adjunctionNhds (⟨x,hU⟩ : (TopCat.of (U:Type u))))
    have hfin : (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).op.Final :=
      Functor.final_op_of_initial _
    exact Functor.Final.colimitIso (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).op
      ((OpenNhds.inclusion x).op ⋙ (toRingSheaf X O).obj)
  -- Underlying `RingEquiv` of the core iso.
  have eCore : restrictStalkRing X O x U hU ≃+*
      ToType (TopCat.Presheaf.stalk ((toRingSheaf X O).obj) x) :=
    coreIso.ringCatIsoToRingEquiv
  -- Reconcile the RingCat-stalk of `toRingSheaf X O` with the CommRingCat-stalk of `O`,
  -- using that `forget₂ CommRingCat RingCat` preserves the (filtered) colimit defining the
  -- stalk; the underlying types agree definitionally.
  have eRecon : ToType (TopCat.Presheaf.stalk ((toRingSheaf X O).obj) x)
      ≃+* ToType (TopCat.Presheaf.stalk O.obj x) :=
    (preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u})
      ((OpenNhds.inclusion x).op ⋙ O.obj)).symm.ringCatIsoToRingEquiv
  exact ⟨eCore.trans eRecon⟩

/-- The **canonical** ring isomorphism `kU := restrictStalkRing X O x U hU ≃+* O_{X,x}`,
the explicit data version of `stalk_restrictRing_ringEquiv` (same cofinality construction).
We expose it as a `def` so that the module-level sub-lemma `stalk_restrictMod_linearEquiv`
and the assembly body of `stalk_linearEquiv_finsupp` use *one and the same* ring iso — the
module-stalk reconciliation is `kU`-linear only with respect to THIS canonical iso (the colimit
comparison), not an arbitrary one. -/
noncomputable def restrictStalkRingEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) {U : Opens X} (hU : x ∈ U) :
    restrictStalkRing X O x U hU ≃+* ToType (TopCat.Presheaf.stalk O.obj x) := by
  have coreIso :
      (@TopCat.Presheaf.stalk RingCat.{u} _ _ (TopCat.of (U : Type u))
        ((restrictRing X U (toRingSheaf X O)).obj) (⟨x, hU⟩ : (U : Type u)))
        ≅ TopCat.Presheaf.stalk (toRingSheaf X O).obj x := by
    have h : IsOpenMap (ConcreteCategory.hom (U.inclusion')) := U.isOpenEmbedding'.isOpenMap
    haveI hinit : (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).Initial :=
      Functor.initial_of_adjunction (h.adjunctionNhds (⟨x,hU⟩ : (TopCat.of (U:Type u))))
    haveI hfin : (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).op.Final :=
      Functor.final_op_of_initial _
    exact Functor.Final.colimitIso (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).op
      ((OpenNhds.inclusion x).op ⋙ (toRingSheaf X O).obj)
  have eCore : restrictStalkRing X O x U hU ≃+*
      ToType (TopCat.Presheaf.stalk ((toRingSheaf X O).obj) x) :=
    coreIso.ringCatIsoToRingEquiv
  have eRecon : ToType (TopCat.Presheaf.stalk ((toRingSheaf X O).obj) x)
      ≃+* ToType (TopCat.Presheaf.stalk O.obj x) :=
    (preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u})
      ((OpenNhds.inclusion x).op ⋙ O.obj)).symm.ringCatIsoToRingEquiv
  exact eCore.trans eRecon

/-- Elementwise form of an equation `f ≫ g = h` in a concrete category. -/
private theorem apply_eq_of_comp_eq {C : Type*} [Category C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (s : ToType X) :
    g (f s) = h s := by
  rw [← e, ConcreteCategory.comp_apply]

set_option maxHeartbeats 4000000 in
-- this proof's elaboration needs more than the default heartbeat budget
-- works around the isDefEq-transparency change (post Lean bump): the germ
-- applications below need `(Opens ↥U)ᵒᵖ ⥤ RingCat` to match `TopCat.Presheaf`.
set_option backward.isDefEq.respectTransparency.types false in
/-- **(Sub-lemma (a): stalk of the restriction = stalk of `F`.)**  The stalk of the restriction
`restrictMod X U R F` at `⟨x,hU⟩ : ↥U` is `kU`-linearly isomorphic to the ambient stalk `F_x`,
where `F_x` is regarded as a `kU`-module via restriction of scalars along the ring iso
`kU ≃+* O_{X,x}` of `stalk_restrictRing_ringEquiv`.

PROOF.  Same cofinality route as the ring reconciliation, carried out on the underlying
`AddCommGrpCat` presheaf of `F` (which `restrictMod` pushes forward), then lifted through the
module structure; compatibility with the ring iso is naturality of the colimit comparison.

NB: the target `F_x` is given its `kU`-module structure via the **canonical** ring iso
`restrictStalkRingEquiv` (the colimit comparison itself), NOT an arbitrary `e` — the additive
colimit-comparison iso is `kU`-linear only for that specific ring iso. -/
theorem Trivialization.stalk_restrictMod_linearEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (F : SheafOfModules.{u} (toRingSheaf X O))
    (x : X) {U : Opens X} (hU : x ∈ U) :
    Nonempty
      (@LinearEquiv (restrictStalkRing X O x U hU) (restrictStalkRing X O x U hU) _ _
        (RingHom.id _) (RingHom.id _) _ _
        (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((restrictMod X U (toRingSheaf X O) F).val.presheaf) (⟨x, hU⟩ : (U : Type u))))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x))
        _ _ _
        (Module.compHom (ToType (TopCat.Presheaf.stalk F.val.presheaf x))
          (restrictStalkRingEquiv X O x hU).toRingHom)) := by
  -- cofinality on the AddCommGrpCat presheaf of `F` + lift through module structure.
  have h : IsOpenMap (ConcreteCategory.hom (U.inclusion')) := U.isOpenEmbedding'.isOpenMap
  have hinit : (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).Initial :=
    Functor.initial_of_adjunction (h.adjunctionNhds (⟨x,hU⟩ : (TopCat.of (U:Type u))))
  have hfin : (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).op.Final :=
    Functor.final_op_of_initial _
  set coreIsoF :
      (@TopCat.Presheaf.stalk AddCommGrpCat.{u} _ _ (TopCat.of (U : Type u))
        ((restrictMod X U (toRingSheaf X O) F).val.presheaf) (⟨x, hU⟩ : (U : Type u)))
        ≅ TopCat.Presheaf.stalk F.val.presheaf x :=
    Functor.Final.colimitIso (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).op
      ((OpenNhds.inclusion x).op ⋙ F.val.presheaf) with hcoreDef
  have hcoreEq : coreIsoF.hom =
      (Functor.Final.colimitIso (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).op
        ((OpenNhds.inclusion x).op ⋙ F.val.presheaf)).hom := by rw [hcoreDef]
  set addE : (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
        ((restrictMod X U (toRingSheaf X O) F).val.presheaf) (⟨x, hU⟩ : (U : Type u)))) ≃+
      ToType (TopCat.Presheaf.stalk F.val.presheaf x) :=
    coreIsoF.addCommGroupIsoToAddEquiv with haddE
  let instTgt : Module (restrictStalkRing X O x U hU)
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    Module.compHom (ToType (TopCat.Presheaf.stalk F.val.presheaf x))
      (restrictStalkRingEquiv X O x hU).toRingHom
  refine ⟨{ toFun := addE
            invFun := addE.symm
            left_inv := addE.left_inv
            right_inv := addE.right_inv
            map_add' := addE.map_add
            map_smul' := ?_ }⟩
  intro c m
  obtain ⟨V, hxV, m₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ m
  obtain ⟨W, hxW, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ c
  -- restrict to the common open `V ⊓ W` of `↥U`
  have hxZ : (⟨x, hU⟩ : (U:Type u)) ∈ V ⊓ W := ⟨hxV, hxW⟩
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_right : V ⊓ W ≤ W)) _ hxZ r₀,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_left : V ⊓ W ≤ V)) _ hxZ m₀]
  set rr : ToType ((restrictRing X U (toRingSheaf X O)).obj.obj (Opposite.op (V ⊓ W))) :=
    (ConcreteCategory.hom ((restrictRing X U (toRingSheaf X O)).obj.map (homOfLE
        (inf_le_right)).op)) r₀ with hrr
  set mm : ToType ((restrictMod X U (toRingSheaf X O) F).val.presheaf.obj (Opposite.op (V ⊓ W))) :=
    (ConcreteCategory.hom ((restrictMod X U (toRingSheaf X O) F).val.presheaf.map (homOfLE
        (inf_le_left)).op)) m₀ with hmm
  rw [← PresheafOfModules.germ_ringCat_smul (restrictMod X U (toRingSheaf X O) F).val (⟨x, hU⟩ :
      (U:Type u)) (V ⊓ W) hxZ rr mm]
  -- membership of x in the image open
  have hximg : x ∈ (inclF X U).obj (V ⊓ W) := ⟨⟨x, hU⟩, hxZ, rfl⟩
  -- key: how `addE` acts on a germ of `P = (restrictMod F).val.presheaf`
  have keyF : ∀ (Z' : Opens (TopCat.of (U:Type u))) (hxZ' : (⟨x, hU⟩ : (U:Type u)) ∈ Z')
      (hximg' : x ∈ (inclF X U).obj Z')
      (s : ToType ((restrictMod X U (toRingSheaf X O) F).val.presheaf.obj (Opposite.op Z'))),
      addE ((ConcreteCategory.hom (TopCat.Presheaf.germ (X := TopCat.of (U : Type u))
          (restrictMod X U (toRingSheaf X O) F).val.presheaf Z' (⟨x, hU⟩ : (U:Type u)) hxZ')) s)
        = (ConcreteCategory.hom
            (TopCat.Presheaf.germ F.val.presheaf ((inclF X U).obj Z') x hximg')) s := by
    intro Z' hxZ' hximg' s
    have hcol := Functor.Final.ι_colimitIso_hom (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).op
      ((OpenNhds.inclusion x).op ⋙ F.val.presheaf) (Opposite.op ⟨Z', hxZ'⟩)
    rw [haddE]
    change (ConcreteCategory.hom coreIsoF.hom) _ = _
    rw [hcoreEq]
    exact apply_eq_of_comp_eq hcol s
  -- rewrite both `addE (germ ...)` via keyF
  rw [keyF (V ⊓ W) hxZ hximg (rr • mm), keyF (V ⊓ W) hxZ hximg mm]
  -- on the F-side, `germ (rr • mm) = (O.val.germ ...) rr • germ mm` (CommRingCat germ_smul)
  rw [PresheafOfModules.germ_smul F.val x ((inclF X U).obj (V ⊓ W)) hximg rr mm]
  -- remaining: (O.val.germ (inclF.obj Z) x) rr • y = (restrictStalkRingEquiv (germ R Z rr)) • y
  congr 1
  -- keyR: restrictStalkRingEquiv intertwines the ring germ with the ambient germ.
  rw [RingHom.id_apply]
  -- reconstruct the canonical ring iso transparently (same `h`, `hinit`, `hfin` in scope)
  have hRE : restrictStalkRingEquiv X O x hU =
      (Functor.Final.colimitIso (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).op
        ((OpenNhds.inclusion x).op ⋙ (toRingSheaf X O).obj)).ringCatIsoToRingEquiv.trans
        (preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u})
          ((OpenNhds.inclusion x).op ⋙ O.obj)).symm.ringCatIsoToRingEquiv := rfl
  rw [hRE]
  -- Names for the two component ring isos.
  set eCoreR := (Functor.Final.colimitIso (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).op
      ((OpenNhds.inclusion x).op ⋙ (toRingSheaf X O).obj)).ringCatIsoToRingEquiv with heCoreR
  set eReconR := (preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u})
      ((OpenNhds.inclusion x).op ⋙ O.obj)).symm.ringCatIsoToRingEquiv with heReconR
  change (ConcreteCategory.hom (TopCat.Presheaf.germ ((sheafToPresheaf (Opens.grothendieckTopology
      X) CommRingCat).obj O)
          ((inclF X U).obj (V ⊓ W)) x hximg)) rr
      = eReconR (eCoreR ((ConcreteCategory.hom (TopCat.Presheaf.germ
          (X := TopCat.of (U : Type u)) (restrictRing X U (toRingSheaf X O)).obj (V ⊓ W)
          (⟨x, hU⟩ : (U:Type u)) hxZ)) rr))
  -- Step A: eCoreR sends the restricted ring-germ to the `toRingSheaf` germ at x.
  have hAcore : eCoreR ((ConcreteCategory.hom (TopCat.Presheaf.germ
      (X := TopCat.of (U : Type u)) (restrictRing X U (toRingSheaf X O)).obj (V ⊓ W)
      (⟨x, hU⟩ : (U:Type u)) hxZ)) rr)
      = (ConcreteCategory.hom
          (TopCat.Presheaf.germ (toRingSheaf X O).obj ((inclF X U).obj (V ⊓ W)) x hximg)) rr := by
    have hcol := Functor.Final.ι_colimitIso_hom (h.functorNhds (⟨x,hU⟩ : (TopCat.of (U:Type u)))).op
      ((OpenNhds.inclusion x).op ⋙ (toRingSheaf X O).obj) (Opposite.op ⟨V ⊓ W, hxZ⟩)
    exact apply_eq_of_comp_eq hcol rr
  rw [hAcore]
  -- Step B: eReconR (forget₂ reconciliation) sends the `toRingSheaf` germ to the `O` germ.
  have hcol := ι_preservesColimitIso_inv (forget₂ CommRingCat.{u} RingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ O.obj) (Opposite.op ⟨(inclF X U).obj (V ⊓ W), hximg⟩)
  have hcol2 := apply_eq_of_comp_eq hcol rr
  change (ConcreteCategory.hom (TopCat.Presheaf.germ ((sheafToPresheaf (Opens.grothendieckTopology
      X) CommRingCat).obj O)
          ((inclF X U).obj (V ⊓ W)) x hximg)) rr
      = (ConcreteCategory.hom (preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u})
          ((OpenNhds.inclusion x).op ⋙ O.obj)).inv)
          ((ConcreteCategory.hom (TopCat.Presheaf.germ (toRingSheaf X O).obj ((inclF X U).obj (V ⊓
              W)) x hximg)) rr)
  exact (hcol2.trans rfl).symm

/-- The stalk of the unit presheaf-of-modules `PresheafOfModules.unit R` (the ring presheaf `R`
regarded as a module over itself) at a point `x` is `R.stalk x`-linearly isomorphic to the ring
stalk `R.stalk x` itself.  The underlying additive isomorphism is the comparison isomorphism for
the forgetful functor `RingCat ⥤ AddCommGrpCat` (which preserves the filtered colimit defining the
stalk), and `R.stalk x`-linearity is multiplication in the ring stalk. -/
noncomputable def unitStalkLEquiv {X : TopCat.{u}} (R : TopCat.Presheaf RingCat.{u} X) (x : X) :
    (ToType (TopCat.Presheaf.stalk (PresheafOfModules.unit R).presheaf x))
      ≃ₗ[ToType (R.stalk x)]
      (ToType (R.stalk x)) := by
  set pIso : (forget₂ RingCat.{u} AddCommGrpCat.{u}).obj (R.stalk x) ≅
      TopCat.Presheaf.stalk (PresheafOfModules.unit R).presheaf x :=
    preservesColimitIso (forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ R) with hpIso
  set addE : (ToType (TopCat.Presheaf.stalk (PresheafOfModules.unit R).presheaf x)) ≃+
      ToType (R.stalk x) := pIso.symm.addCommGroupIsoToAddEquiv with haddE
  have key : ∀ (U : Opens X) (hxU : x ∈ U) (s : ToType ((PresheafOfModules.unit R).presheaf.obj
      (Opposite.op U))),
      addE ((ConcreteCategory.hom (TopCat.Presheaf.germ (PresheafOfModules.unit R).presheaf U x
          hxU)) s)
      = (ConcreteCategory.hom (R.germ U x hxU)) s := by
    intro U hxU s
    have h := ι_preservesColimitIso_inv (forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ R) (Opposite.op ⟨U, hxU⟩)
    rw [← hpIso] at h
    have h2 := congrArg (fun (f : _ ⟶ _) => (ConcreteCategory.hom f) s) h
    simp only [ConcreteCategory.comp_apply] at h2
    change (ConcreteCategory.hom pIso.inv)
        ((ConcreteCategory.hom (colimit.ι (((OpenNhds.inclusion x).op ⋙ R) ⋙ forget₂ RingCat.{u}
            AddCommGrpCat.{u}) (Opposite.op ⟨U, hxU⟩))) s)
        = (ConcreteCategory.hom ((forget₂ RingCat.{u} AddCommGrpCat.{u}).map (colimit.ι
            ((OpenNhds.inclusion x).op ⋙ R) (Opposite.op ⟨U, hxU⟩)))) s
    exact h2
  refine
    { toFun := addE
      invFun := addE.symm
      left_inv := addE.left_inv
      right_inv := addE.right_inv
      map_add' := addE.map_add
      map_smul' := ?_ }
  intro r m
  obtain ⟨U, hxU, m₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq (PresheafOfModules.unit R).presheaf m
  obtain ⟨V, hxV, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
  set W : Opens X := U ⊓ V with hW
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  have hr : (ConcreteCategory.hom (R.germ V x hxV)) r₀
      = (ConcreteCategory.hom (R.germ W x hxW))
          ((ConcreteCategory.hom (R.map (homOfLE (inf_le_right)).op)) r₀) := by
    rw [TopCat.Presheaf.germ_res_apply]
  have hm : (ConcreteCategory.hom (TopCat.Presheaf.germ (PresheafOfModules.unit R).presheaf U x
      hxU)) m₀
      = (ConcreteCategory.hom (TopCat.Presheaf.germ (PresheafOfModules.unit R).presheaf W x hxW))
          ((ConcreteCategory.hom
              ((PresheafOfModules.unit R).presheaf.map (homOfLE (inf_le_left)).op)) m₀) := by
    rw [TopCat.Presheaf.germ_res_apply]
  rw [hr, hm]
  set rr : ToType (R.obj (Opposite.op W)) := (ConcreteCategory.hom (R.map (homOfLE
      (inf_le_right)).op)) r₀ with hrr
  set mm : ToType ((PresheafOfModules.unit R).presheaf.obj (Opposite.op W)) :=
    (ConcreteCategory.hom ((PresheafOfModules.unit R).presheaf.map (homOfLE (inf_le_left)).op)) m₀
        with hmm
  rw [← PresheafOfModules.germ_ringCat_smul (PresheafOfModules.unit R) x W hxW rr mm]
  rw [key W hxW (rr • mm), key W hxW mm]
  dsimp only [RingHom.id_apply]
  have e1 : (rr • mm : ToType ((PresheafOfModules.unit R).presheaf.obj (Opposite.op W)))
      = (rr • (mm : ToType (R.obj (Opposite.op W))) : ToType (R.obj (Opposite.op W))) := rfl
  rw [e1, smul_eq_mul, map_mul, smul_eq_mul]

/-- The identification of the stalk of the unit presheaf of modules with the ring stalk sends
the germ of a section to its germ as a function. -/
theorem unitStalkLEquiv_germ {X : TopCat.{u}}
    (R : X.Presheaf RingCat.{u}) (x : X) (U : Opens X) (hx : x ∈ U) (r : R.obj (.op U)) :
    LocallyFreeRank.unitStalkLEquiv R x
        (TopCat.Presheaf.germ (PresheafOfModules.unit R).presheaf U x hx r) =
      R.germ U x hx r :=
  congrArg (fun f => (ConcreteCategory.hom f) r)
    (ι_preservesColimitIso_inv (forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ R) (.op ⟨U, hx⟩))

/-- **(Sub-lemma (b.1): stalk of the unit sheaf = the stalk ring.)**  The stalk at `⟨x,hU⟩ : ↥U`
of the underlying presheaf of `SheafOfModules.unit (restrictRing X U (toRingSheaf X O))` is
`kU`-linearly isomorphic to `kU` itself (the rank-one free module).

This is the third bridge of the stalk computation: `unit R` is the ring sheaf `R` regarded as a
module over itself; its underlying `AddCommGrpCat` presheaf is the additive group of `R.val`,
so its `Ab`-stalk is the additive group of the ring stalk `kU = stalk R.val ⟨x,hU⟩` (the
forgetful functor `RingCat ⥤ AddCommGrpCat` preserves the filtered colimit defining the stalk),
and the `kU`-module structure is multiplication in `kU`.  Likely route: identify
`(unit R).val.presheaf` with `(forget₂ RingCat AddCommGrpCat).mapPresheaf R.val` (definitionally
/ via the `unit` API), then the stalk-module structure on `unit` is `kU` acting on itself. -/
theorem Trivialization.stalk_unit_linearEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) {U : Opens X} (hU : x ∈ U) :
    Nonempty
      ((ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val.presheaf)
          (⟨x, hU⟩ : (U : Type u))))
        ≃ₗ[restrictStalkRing X O x U hU]
        (restrictStalkRing X O x U hU)) := by
  -- SANITY CHECK PASSED ...
  refine ⟨?_⟩
  exact unitStalkLEquiv (X := TopCat.of (U : Type u))
    (R := (restrictRing X U (toRingSheaf X O)).obj) (x := (⟨x, hU⟩ : (U : Type u)))

/-- The `kU := restrictStalkRing`-module structure on the stalk of the **presheaf-level**
coproduct `∐ (fun _ : ι => (SheafOfModules.unit S).val)` (taken in `PresheafOfModules S.val`),
at `⟨x,hU⟩ : ↥U`.  Named (analogously to `instModuleStalkFree`) so that the `≃ₗ[kU]` statements
of the two b.2 bridge sub-lemmas elaborate. -/
noncomputable instance instModuleStalkPresheafCoprod
    (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) (U : Opens X) (hU : x ∈ U) (ι : Type u) :
    Module (restrictStalkRing X O x U hU)
      (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((∐ (fun _ : ι => (SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val)
            : PresheafOfModules.{u} ((restrictRing X U (toRingSheaf X O)).obj)).presheaf)
          (⟨x, hU⟩ : (U : Type u)))) :=
  PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier
    (X := TopCat.of (U : Type u))
    (R := (restrictRing X U (toRingSheaf X O)).obj)
    (∐ (fun _ : ι => (SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val)
      : PresheafOfModules.{u} ((restrictRing X U (toRingSheaf X O)).obj))
    (⟨x, hU⟩ : (U : Type u))

/-- A morphism `f : P ⟶ Q` of `AddCommGrpCat`-presheaves over the open-cover Grothendieck
topology of a space `X` that is *locally injective* and *locally surjective* induces a
**bijection on every topological stalk**.  (The germ argument: lift germs to representatives on
common opens; local injectivity makes the equalizer sieve a cover, so equal germs descend to a
smaller open; local surjectivity makes the image sieve a cover, so every germ of `Q` is hit.)
This is the stalkwise-isomorphism property of a local isomorphism, used to discharge Bridge (I)
(stalk invariance under sheafification). -/
theorem stalkFunctor_bijective_of_locally_bijective
    {X : TopCat.{u}} {P Q : TopCat.Presheaf AddCommGrpCat.{u} X} (f : P ⟶ Q)
    (hinj : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) f)
    (hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f) (x : X) :
    Function.Bijective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f)) := by
  constructor
  · -- injective
    intro a b hab
    obtain ⟨U, hxU, sa, rfl⟩ := TopCat.Presheaf.exists_germ_eq P a
    obtain ⟨U', hxU', sb, rfl⟩ := TopCat.Presheaf.exists_germ_eq P b
    have hxW0 : x ∈ U ⊓ U' := ⟨hxU, hxU'⟩
    rw [← TopCat.Presheaf.germ_res_apply P (homOfLE inf_le_left) x hxW0 sa,
      ← TopCat.Presheaf.germ_res_apply P (homOfLE inf_le_right) x hxW0 sb] at hab ⊢
    generalize (ConcreteCategory.hom (P.map (homOfLE inf_le_left).op)) sa = sa' at hab ⊢
    generalize (ConcreteCategory.hom (P.map (homOfLE inf_le_right).op)) sb = sb' at hab ⊢
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply _ x hxW0 f sa',
      TopCat.Presheaf.stalkFunctor_map_germ_apply _ x hxW0 f sb'] at hab
    obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq Q x hxW0 hxW0 _ _ hab
    rw [← NatTrans.naturality_apply f iU.op, ← NatTrans.naturality_apply f iV.op] at hW
    obtain ⟨V2, j, hj, hxV2⟩ := (hinj.equalizerSieve_mem _ _ hW) x hxW
    rw [← TopCat.Presheaf.germ_res_apply P (j ≫ iU) x hxV2 sa',
      ← TopCat.Presheaf.germ_res_apply P (j ≫ iV) x hxV2 sb']
    congr 1
    simpa [op_comp, Functor.map_comp] using hj
  · -- surjective
    intro t
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq Q t
    have hsieve := hsurj.imageSieve_mem (U := U) s
    obtain ⟨V, i, ⟨u, hu⟩, hxV⟩ := hsieve x hxU
    refine ⟨(ConcreteCategory.hom (P.germ V x hxV)) u, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV f u]
    rw [hu]
    rw [TopCat.Presheaf.germ_res_apply Q i x hxV s]

set_option maxHeartbeats 2000000 in
-- this proof's elaboration needs more than the default heartbeat budget
/-- **(b.2 Bridge (I): the sheaf coproduct and the presheaf coproduct have the SAME stalk.)**
The stalk at `⟨x,hU⟩ : ↥U` of the underlying presheaf of the *sheaf* coproduct `free ι`
(`= ∐^{Sheaf} unit`) is `kU`-linearly isomorphic to the stalk of the *presheaf-level* coproduct
`∐^{psh} (unit.val)` (taken in `PresheafOfModules ((restrictRing …).val)`).

THIS IS THE SUBSTANTIVE OBSTRUCTION.
`free ι = ∐^{Sheaf} unit` and the underlying presheaf of a sheaf coproduct is the
*sheafification* of the presheaf coproduct.  The sheafification unit `η : ∐^{psh} unit.val ⟶
(free ι).val` (an `S.val`-`PresheafOfModules` morphism, the comparison from `isColimitFreeCofan`
through the forgetful functor) is a *local isomorphism* for `Opens.grothendieckTopology ↥U`,
hence induces an **isomorphism on every topological stalk** (the stalk is invariant under
sheafification).  PROOF ROUTE (closer's recommended decomposition):
* build `η` as the canonical map `∐^{psh} unit.val ⟶ (free ι).val` (the comparison of the
  presheaf coproduct cocone with the image of `freeCofan ι` under the forgetful functor
  `SheafOfModules.forget` — both are cocones under `fun _ => unit.val`);
* show `η` is locally injective + locally surjective (`Presheaf.IsLocallyInjective`/
  `IsLocallySurjective` for the sheafification unit `toSheafify`), so `(stalkFunctor Ab
  ⟨x,hU⟩).map η.app...` is an iso (via `stalkFunctor_map_injective_of_app_injective` +
  `app_surjective_of_stalkFunctor_map_bijective`-style germ lemmas, confirmed available for
  `AddCommGrpCat`);
* upgrade the additive stalk iso to `kU`-linear via `stalkLMap`/germ-`smul` compatibility
  (`PresheafOfModules.germ_ringCat_smul`, as in `unitStalkLEquiv`/`stalkLMap`). -/
theorem Trivialization.stalk_free_presheafCoprod_linearEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) {U : Opens X} (hU : x ∈ U)
    (ι : Type u) :
    Nonempty
      ((ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((SheafOfModules.free.{u} (R := restrictRing X U (toRingSheaf X O)) ι).val.presheaf)
          (⟨x, hU⟩ : (U : Type u))))
        ≃ₗ[restrictStalkRing X O x U hU]
        (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((∐ (fun _ : ι => (SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val)
            : PresheafOfModules.{u} ((restrictRing X U (toRingSheaf X O)).obj)).presheaf)
          (⟨x, hU⟩ : (U : Type u))))) := by
  -- SANITY CHECK PASSED  (inherits b.2's check: this is the additive-iso Bridge (I) half of the
  -- already-sanity-checked b.2; both sides carry the same kU-module structure via the named
  -- PresheafOfModules stalk-module instances; statement is the standard "stalk invariant under
  -- sheafification" fact, true and well-encoded.)
  -- Bridge (I): η : ∐^psh unit.val ⟶ (free ι).val is a local iso (sheafification unit), so it
  -- induces an iso on the stalk at ⟨x,hU⟩; upgrade to kU-linear via germ-smul compatibility.
  classical
  set Y : TopCat.{u} := TopCat.of (U : Type u) with hY
  set p : (Y : Type u) := (⟨x, hU⟩ : (U : Type u)) with hp
  set R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u} := restrictRing X U (toRingSheaf X O)
      with hR
  set unitS : SheafOfModules.{u} R := SheafOfModules.unit R with hunitS
  set Pfam : ι → PresheafOfModules.{u} R.obj := fun _ => unitS.val with hPfam
  -- the comparison `η : ∐^psh unit.val ⟶ (free ι).val` of the presheaf-coproduct cocone with the
  -- image of `freeCofan` under `SheafOfModules.forget` (both cocones under `fun _ => unit.val`).
  set cocone : ∀ i, Pfam i ⟶ (SheafOfModules.free.{u} (R := R) ι).val :=
    fun i => (SheafOfModules.forget R).map (Limits.Sigma.ι (fun _ : ι => unitS) i) with hcocone
  set η : (∐ Pfam : PresheafOfModules.{u} R.obj) ⟶ (SheafOfModules.free.{u} (R := R) ι).val :=
    Limits.Sigma.desc cocone with hη
  -- STEP 1: `η` becomes an isomorphism after the presheaf-of-modules sheafification `SF`.
  -- `SF` is a left adjoint, hence preserves the coproduct `∐ Pfam`; and `forget ⋙ SF ≅ 𝟭`
  -- (the counit is an iso, as `forget` is fully faithful and `restrictScalars (𝟙) = 𝟭`), so
  -- `forget ⋙ SF` also preserves the coproduct of `unitS`.  Both sides are then colimits with
  -- matching injections, so the comparison `SF.map η` is an iso.
  set SF := PresheafOfModules.sheafification (𝟙 R.obj) with hSF
  set adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj) with hadj
  have : SF.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have : PreservesColimitsOfShape (Discrete ι) SF := by infer_instance
  let εIso : (SheafOfModules.forget R ⋙ SF) ≅ 𝟭 _ :=
    (eqToIso (rfl : (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) ⋙ SF
      = (SheafOfModules.forget R ⋙ SF)).symm) ≪≫ asIso adj.counit
  have : PreservesColimitsOfShape (Discrete ι) (SheafOfModules.forget R ⋙ SF) :=
    preservesColimitsOfShape_of_natIso εIso.symm
  have hLc : IsColimit (SF.mapCocone (Cofan.mk (∐ Pfam) (Limits.Sigma.ι Pfam))) :=
    isColimitOfPreserves SF (coproductIsCoproduct Pfam)
  have hRc : IsColimit ((SheafOfModules.forget R ⋙ SF).mapCocone
      (Cofan.mk (∐ (fun _ : ι => unitS)) (Limits.Sigma.ι (fun _ : ι => unitS)))) :=
    isColimitOfPreserves (SheafOfModules.forget R ⋙ SF) (coproductIsCoproduct (fun _ : ι => unitS))
  let dnat : (Discrete.functor Pfam ⋙ SF)
      ≅ (Discrete.functor (fun _ : ι => unitS) ⋙ (SheafOfModules.forget R ⋙ SF)) :=
    Discrete.natIso (fun _ => Iso.refl _)
  let Φ := IsColimit.coconePointsIsoOfNatIso hLc hRc dnat
  have hΦ : Φ.hom = SF.map η := by
    refine hLc.hom_ext (fun jj => ?_)
    obtain ⟨i⟩ := jj
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom hLc hRc dnat ⟨i⟩]
    have hd : dnat.hom.app ⟨i⟩ = 𝟙 _ := by
      simp only [dnat, Discrete.natIso_hom_app, Iso.refl_hom]
    rw [hd, Category.id_comp]
    simp only [Functor.mapCocone_ι_app, Cofan.mk_ι_app, Functor.comp_map]
    rw [← SF.map_comp]
    congr 1
    rw [Limits.colimit.ι_desc]
    rfl
  have hSFiso : IsIso (SF.map η) := hΦ ▸ Φ.isIso_hom
  -- STEP 2: descend to the underlying `Ab`-presheaf morphism `ηp := toPresheaf.map η`.  Because
  -- `sheafification ⋙ toSheaf = toPresheaf ⋙ presheafToSheaf` (definitionally), the iso `SF.map η`
  -- gives `IsIso (presheafToSheaf.map ηp)`, i.e. `η` is in the class `J.W`.
  set ηp := (PresheafOfModules.toPresheaf R.obj).map η with hηp
  have hpsiso : IsIso ((presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map ηp) :=
    (inferInstance : IsIso ((SheafOfModules.toSheaf R).map (SF.map η)))
  have hW : (Opens.grothendieckTopology Y).W ηp := (GrothendieckTopology.W_iff _ ηp).mpr hpsiso
  -- STEP 3: `J.W = locally injective ∧ locally surjective`; apply the germ bijectivity lemma.
  obtain ⟨hinj, hsurj⟩ :=
    (⟨hW.isLocallyInjective, hW.isLocallySurjective⟩ :
      Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y) ηp ∧
        Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) ηp)
  have hbij := stalkFunctor_bijective_of_locally_bijective ηp hinj hsurj p
  -- STEP 4: `stalkLMap η p` is a `kU`-linear map whose underlying function is the (bijective)
  -- stalk map of `ηp`; package it as a `LinearEquiv` and take `.symm` (η goes presheaf-coprod →
  -- free, so its stalk map goes presheaf-coprod-stalk → free-stalk; the goal wants the reverse).
  have hg : (stalkLMap η p : _ → _) =
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).map ηp)) := rfl
  exact ⟨(LinearEquiv.ofBijective (stalkLMap η p) (by rw [hg]; exact hbij)).symm⟩

/-- **(b.2 Bridges (II)+(III)+(IV): stalk of the presheaf coproduct = direct sum of unit-stalks.)**
The stalk at `⟨x,hU⟩ : ↥U` of the *presheaf-level* coproduct `∐^{psh} (unit.val)` (in
`PresheafOfModules ((restrictRing …).val)`) is `kU`-linearly isomorphic to the direct sum
`⨁ (_ : ι), (unit-stalk)`.

This is the TRACTABLE half (no sheafification).  PROOF ROUTE:
* `PresheafOfModules.toPresheaf` preserves colimits (confirmed:
`preservesColimitsOfSize_of_univLE`),
  so `(∐^{psh} unit.val).presheaf ≅ ∐^{psh,Ab} (unit.val.presheaf)` (coproduct in
  `TopCat.Presheaf Ab ↥U`);
* `TopCat.Presheaf.stalkFunctor AddCommGrpCat ⟨x,hU⟩` `PreservesColimits` (by `inferInstance`),
  so via `preservesColimitIso` / `isColimitOfPreserves` the stalk of that presheaf coproduct is
  the `Ab`-coproduct `∐^{Ab}_ι (stalk (unit.val.presheaf) ⟨x,hU⟩)`;
* identify the `Ab`-coproduct with `⨁` via `ModuleCat.coprodIsoDirectSum` (at the `ModuleCat kU`
  level, where the comparison maps are `LinearEquiv`s);
* thread `kU`-linearity throughout (perform the comparison isos at `ModuleCat kU` level). -/
theorem Trivialization.stalk_presheafCoprod_directSum_linearEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) {U : Opens X} (hU : x ∈ U)
    (ι : Type u) :
    Nonempty
      ((ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((∐ (fun _ : ι => (SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val)
            : PresheafOfModules.{u} ((restrictRing X U (toRingSheaf X O)).obj)).presheaf)
          (⟨x, hU⟩ : (U : Type u))))
        ≃ₗ[restrictStalkRing X O x U hU]
        (DirectSum ι (fun _ : ι =>
          (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
            ((SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val.presheaf)
            (⟨x, hU⟩ : (U : Type u))))))) := by
  -- SANITY CHECK PASSED  (inherits b.2's check: tractable presheaf-coproduct half, no
  -- sheafification; toPresheaf + stalkFunctor both preserve the Discrete ι colimit, so the
  -- stalk of the presheaf coproduct is the Ab/kU-coproduct of unit-stalks = ⨁; well-encoded.)
  -- Bridges (II)+(III)+(IV): toPresheaf preserves coprod ⇒ stalk of presheaf-coprod = ∐ stalks;
  -- stalkFunctor preserves coprod; ModuleCat.coprodIsoDirectSum to land at ⨁.
  classical
  set Y : TopCat.{u} := TopCat.of (U : Type u) with hY
  set p : (Y : Type u) := (⟨x, hU⟩ : (U : Type u)) with hp
  set S : TopCat.Presheaf RingCat.{u} Y := (restrictRing X U (toRingSheaf X O)).obj with hS
  set unitval : PresheafOfModules.{u} S :=
    (SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val with hunit
  set C : PresheafOfModules.{u} S := ∐ (fun _ : ι => unitval) with hC
  set G : PresheafOfModules.{u} S ⥤ AddCommGrpCat.{u} :=
    (PresheafOfModules.toPresheaf S) ⋙ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p) with hG
  have hpc : PreservesColimit (Discrete.functor (fun _ : ι => unitval)) G := by
    have h1 : PreservesColimit (Discrete.functor (fun _ : ι => unitval))
        (PresheafOfModules.toPresheaf S) := inferInstance
    have h2 : PreservesColimit
        ((Discrete.functor (fun _ : ι => unitval)) ⋙ PresheafOfModules.toPresheaf S)
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p) :=
      (inferInstance : PreservesColimits (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p)
        ).preservesColimitsOfShape.preservesColimit
    exact comp_preservesColimit (PresheafOfModules.toPresheaf S)
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p)
  -- The kU-linear assembled map: ⨁ → stalk(C.presheaf) p, built from the stalk-maps of the
  -- coproduct injections.  This is manifestly kU-linear.
  set kU : Type u := restrictStalkRing X O x U hU with hkU
  set P : ι → PresheafOfModules.{u} S := fun _ => unitval with hP
  set g : (DirectSum ι (fun _ : ι =>
      (ToType (TopCat.Presheaf.stalk (X := Y)
        (unitval.presheaf) p)))) →ₗ[kU]
      (ToType (TopCat.Presheaf.stalk (X := Y) (C.presheaf) p)) :=
    DirectSum.toModule kU ι _ (fun i => stalkLMap (Limits.Sigma.ι P i) p) with hg
  -- The additive comparison iso from the two colimit cocones over `Discrete.functor P ⋙ G`.
  have hcol : IsColimit (G.mapCocone (Cofan.mk (∐ P) (Limits.Sigma.ι P))) :=
    isColimitOfPreserves G (coproductIsCoproduct P)
  -- The DirectSum colimit cocone on the family `fun i => G.obj (P i)`.
  set M : ι → Type u := fun _ => ToType (TopCat.Presheaf.stalk (X := Y) (unitval.presheaf) p)
    with hM
  set Dpt : AddCommGrpCat.{u} := AddCommGrpCat.of (DirectSum ι (fun i => M i)) with hDpt
  set Dcofan : Cofan (fun i => G.obj (P i)) :=
    Cofan.mk Dpt (fun i => AddCommGrpCat.ofHom (DirectSum.lof kU ι M i).toAddMonoidHom) with hDcofan
  have Dcol : IsColimit Dcofan := by
    refine Cofan.IsColimit.mk Dcofan
      (fun t => AddCommGrpCat.ofHom
        (DirectSum.toAddMonoid (fun i => (t.inj i).hom))) ?_ ?_
    · intro t i
      ext m
      change (DirectSum.toAddMonoid (fun i => (t.inj i).hom))
        ((DirectSum.of M i) m) = (t.inj i).hom m
      exact DirectSum.toAddMonoid_of (fun i => (t.inj i).hom) i m
    · intro t m hm
      ext z
      change m.hom z = (DirectSum.toAddMonoid (fun i => (t.inj i).hom)) z
      have key : m.hom = (DirectSum.toAddMonoid (fun i => (t.inj i).hom) :
          (DirectSum ι (fun i => M i)) →+ _) := by
        refine DirectSum.addHom_ext (β := M) (fun i y => ?_)
        have h2 := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (hm i)) y
        change m.hom ((DirectSum.of M i) y) = (DirectSum.toAddMonoid (fun i => (t.inj i).hom))
          ((DirectSum.of M i) y)
        have hrhs : (DirectSum.toAddMonoid (fun i => (t.inj i).hom))
            ((DirectSum.of M i) y) = (t.inj i).hom y :=
          DirectSum.toAddMonoid_of (fun i => (t.inj i).hom) i y
        rw [hrhs]
        change m.hom ((DirectSum.lof kU ι M i) y) = (t.inj i).hom y
        rw [show (DirectSum.lof kU ι M i) y = (Dcofan.inj i).hom y from rfl, ← h2]
        rfl
      exact DFunLike.congr_fun key z
  -- The additive comparison iso `stalk(C.presheaf) p ≅ DirectSum` (carrier Dpt).
  set Φ := IsColimit.coconePointsIsoOfNatIso hcol Dcol
    (Discrete.natIso (fun _ => Iso.refl _)) with hΦ
  -- `g` agrees with `Φ.inv` as a function, hence is bijective.
  have hgeq : (g : (DirectSum ι (fun i => M i)) → _) = Φ.inv.hom := by
    have hext : g.toAddMonoidHom = Φ.inv.hom := by
      refine DirectSum.addHom_ext (β := M) (fun i y => ?_)
      have hfac := IsColimit.comp_coconePointsIsoOfNatIso_inv hcol Dcol
        (Discrete.natIso (fun _ => Iso.refl _)) ⟨i⟩
      have hfac2 := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom hfac) y
      -- LHS of hfac2: (Dcofan.inj i ≫ Φ.inv).hom y = Φ.inv.hom (lof i y)
      -- RHS: (𝟙 ≫ G.map (Sigma.ι P i)).hom y = (G.map (Sigma.ι P i)).hom y
      change (g.toAddMonoidHom) ((DirectSum.of M i) y) = Φ.inv.hom ((DirectSum.of M i) y)
      have hg1 : (g.toAddMonoidHom) ((DirectSum.of M i) y)
          = (stalkLMap (Limits.Sigma.ι P i) p) y := by
        change g ((DirectSum.of M i) y) = _
        rw [hg]
        rw [show (DirectSum.of M i) y = (DirectSum.lof kU ι M i) y from rfl]
        rw [DirectSum.toModule_lof]
      -- both sides equal (G.map (Sigma.ι P i)).hom y
      have hL : (stalkLMap (Limits.Sigma.ι P i) p) y = (G.map (Limits.Sigma.ι P i)).hom y := rfl
      have hR : Φ.inv.hom ((DirectSum.of M i) y) = (G.map (Limits.Sigma.ι P i)).hom y := by
        have hfac2' : Φ.inv.hom ((DirectSum.lof kU ι M i) y)
            = ((Discrete.natIso (fun _ => Iso.refl ((Discrete.functor P ⋙ G).obj _))).inv.app
                ⟨i⟩ ≫ (G.mapCocone (Cofan.mk (∐ P) (Limits.Sigma.ι P))).ι.app ⟨i⟩).hom y := by
          have := hfac2
          exact this
        change Φ.inv.hom ((DirectSum.lof kU ι M i) y) = _
        rw [hfac2']
        rfl
      rw [hg1, hL, hR]
    exact congrArg (fun (f : _ →+ _) => (f : _ → _)) hext
  have hbij : Function.Bijective (g : (DirectSum ι (fun i => M i)) → _) := by
    rw [hgeq]
    exact (ConcreteCategory.bijective_of_isIso Φ.inv)
  exact ⟨(LinearEquiv.ofBijective g hbij).symm⟩

/-- **(Sub-lemma (b.2): stalk of free = direct sum of unit-stalks.)**  The stalk at `⟨x,hU⟩ : ↥U`
of the free sheaf `SheafOfModules.free ι` (over the restricted ring sheaf) is `kU`-linearly
isomorphic to the direct sum `⨁ (_ : ι), (unit-stalk)`, where `unit-stalk` is the stalk of
`SheafOfModules.unit`.

This packages the first two bridges of the stalk computation (the substantive content):
`free ι = ∐ (fun _ : ι => unit)` in `SheafOfModules R` (`isColimitFreeCofan`); the underlying
`Ab`-presheaf of this *sheaf* coproduct is the *sheafification* of the presheaf coproduct (so
the forgetful functor does NOT directly preserve it), but the topological stalk is invariant
under sheafification, and `stalkFunctor AddCommGrpCat ⟨x,hU⟩` (which `PreservesColimits` by
`inferInstance`) preserves the presheaf coproduct.  Hence the stalk of `free ι` is the `Ab`/
`kU`-coproduct of the stalks of `unit`, identified with `DirectSum` via
`ModuleCat.coprodIsoDirectSum`.
The crux obligation is reconciling the *site* sheafification for `Opens.grothendieckTopology ↥U`
with the space-level `TopCat.Presheaf` stalk so a sheafification-stalk-iso applies. -/
theorem Trivialization.stalk_free_directSum_linearEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) {U : Opens X} (hU : x ∈ U)
    (ι : Type u) :
    Nonempty
      ((ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((SheafOfModules.free.{u} (R := restrictRing X U (toRingSheaf X O)) ι).val.presheaf)
          (⟨x, hU⟩ : (U : Type u))))
        ≃ₗ[restrictStalkRing X O x U hU]
        (DirectSum ι (fun _ : ι =>
          (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
            ((SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val.presheaf)
            (⟨x, hU⟩ : (U : Type u))))))) := by
  -- SANITY CHECK PASSED  (lean-sanity-check: statement plausible, no counterexample/encoding
  -- defect; LHS module instance = instModuleStalkFree, RHS summands = instModuleStalkUnit, both
  -- via the same base ring; ≃ₗ[kU] elaborates; downstream stalk_free_linearEquiv composes it
  -- correctly; edge cases ι empty/singleton/infinite and kU=0 all consistent.)
  -- ASSEMBLY (Bridge (I) ∘ Bridges (II)+(III)+(IV)): compose the two bridge sub-lemmas.
  obtain ⟨eI⟩ := Trivialization.stalk_free_presheafCoprod_linearEquiv X O x hU ι
  obtain ⟨eII⟩ := Trivialization.stalk_presheafCoprod_directSum_linearEquiv X O x hU ι
  exact ⟨eI.trans eII⟩

/-- The stalk of `SheafOfModules.free ι` over the restricted ring sheaf, at `⟨x, hU⟩ : ↥U`, is
`kU`-linearly isomorphic to the free module `ι →₀ kU`. -/
theorem Trivialization.stalk_free_linearEquiv
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (x : X) {U : Opens X} (hU : x ∈ U)
    (ι : Type u) :
    Nonempty
      ((ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((SheafOfModules.free.{u} (R := restrictRing X U (toRingSheaf X O)) ι).val.presheaf)
          (⟨x, hU⟩ : (U : Type u))))
        ≃ₗ[restrictStalkRing X O x U hU]
        (ι →₀ restrictStalkRing X O x U hU)) := by
  -- SANITY CHECK PASSED  (lean-sanity-check: statement plausible, no counterexample/encoding
  -- defect; LHS module instance defeq to instModuleStalkFree, same ι and kU both sides, single
  -- universe; holds for empty/singleton/infinite ι and even kU=0.)
  classical
  -- (b.2): free-stalk ≃ₗ[kU] ⨁ (_ : ι), (unit-stalk)
  obtain ⟨eDS⟩ := Trivialization.stalk_free_directSum_linearEquiv X O x hU ι
  -- (b.1): unit-stalk ≃ₗ[kU] kU
  obtain ⟨eUnit⟩ := Trivialization.stalk_unit_linearEquiv X O x hU
  -- ⨁ (unit-stalk) ≃ₗ[kU] ⨁ (_ : ι), kU, applying eUnit summandwise
  let eCongr :
      (DirectSum ι (fun _ : ι =>
        (ToType (TopCat.Presheaf.stalk (X := TopCat.of (U : Type u))
          ((SheafOfModules.unit (restrictRing X U (toRingSheaf X O))).val.presheaf)
          (⟨x, hU⟩ : (U : Type u))))))
        ≃ₗ[restrictStalkRing X O x U hU]
        (DirectSum ι (fun _ : ι => restrictStalkRing X O x U hU)) :=
    DirectSum.congrLinearEquiv (fun _ : ι => eUnit)
  -- Final: ⨁ (_ : ι), kU ≃ₗ[kU] (ι →₀ kU)
  refine ⟨eDS.trans (eCongr.trans (finsuppLEquivDirectSum
    (restrictStalkRing X O x U hU) (restrictStalkRing X O x U hU) ι).symm)⟩

set_option maxHeartbeats 4000000 in
-- this proof's elaboration needs more than the default heartbeat budget
/-- **(Crux helper_01c9.)**  A trivialisation `t : F|_U ≅ ⊕_{i∈t.ι} O_X|_U` over an open `U ∋ x`
induces, on passing to stalks at `x`, an `O_{X,x}`-linear equivalence of the stalk `F_x`
with the free `O_{X,x}`-module `t.ι →₀ O_{X,x}`.

ASSEMBLY (from the three sub-lemmas above + verified `stalkLEquivOfIso`):
* `e : kU ≃+* k` from `stalk_restrictRing_ringEquiv`.
* `stalkLEquivOfIso ((SheafOfModules.forget _).mapIso t.iso) ⟨x,hU⟩` gives the middle
  `kU`-linear equiv `(restrictMod)-stalk ≃ₗ[kU] (free t.ι)-stalk` (NB: `t.iso` is a
  `SheafOfModules` iso; push it to the underlying `PresheafOfModules` iso via the forgetful
  functor, then apply the verified `stalkLEquivOfIso`).
* sub-lemma (a) `ea : (restrictMod)-stalk ≃ₗ[kU] F_x` (with `F_x` a `kU`-module via `e`).
* sub-lemma (b) `eb : (free t.ι)-stalk ≃ₗ[kU] (t.ι →₀ kU)`.
* Compose `ea.symm ≪ mid ≪ eb : F_x ≃ₗ[kU] (t.ι →₀ kU)`, then transport scalars along
  `e : kU ≃+* k` (with `Finsupp.mapRange.linearEquiv`/`LinearEquiv` semilinear-cast) to get
  the `k`-linear equiv `F_x ≃ₗ[k] (t.ι →₀ k)`. -/
theorem Trivialization.stalk_linearEquiv_finsupp
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (F : SheafOfModules.{u} (toRingSheaf X O))
    (x : X) {U : Opens X} (hU : x ∈ U)
    (t : Trivialization X (toRingSheaf X O) F U) :
    Nonempty (ToType (TopCat.Presheaf.stalk F.val.presheaf x)
      ≃ₗ[ToType (TopCat.Presheaf.stalk O.obj x)]
      (t.ι →₀ ToType (TopCat.Presheaf.stalk O.obj x))) := by
  -- SANITY CHECK PASSED  (lean-sanity-check: statement plausible, no counterexample/encoding
  -- defect; both sides are O_{X,x}-modules, index set t.ι preserved exactly, single universe.
  -- Caveat: helper_01c9 `stalkPushforward_iso_of_isInducing` does NOT exist verbatim — sub-lemmas
  -- (ring)/(a) build the inducing-stalk iso by hand via the cofinality route.)
  classical
  let e := restrictStalkRingEquiv X O x hU
  obtain ⟨ea⟩ := Trivialization.stalk_restrictMod_linearEquiv X O F x hU
  obtain ⟨eb⟩ := Trivialization.stalk_free_linearEquiv X O x hU t.ι
  -- Assemble: middle `kU`-linear equiv from `stalkLEquivOfIso` of `t.iso`, compose with
  -- `ea`,`eb`, then transport scalars along `e : kU ≃+* k`.  This final assembly threads the
  -- `Module.compHom` `kU`-structure on `F_x` and the semilinear transport on `t.ι →₀ —`.
  let mid := stalkLEquivOfIso (X := TopCat.of (U : Type u))
    (R := (restrictRing X U (toRingSheaf X O)).obj)
    ((SheafOfModules.forget (restrictRing X U (toRingSheaf X O))).mapIso t.iso)
    (⟨x, hU⟩ : (U : Type u))
  let g := ea.symm.trans (mid.trans eb)
  -- `g : F_x ≃ₗ[kU] (t.ι →₀ kU)`, with F_x carrying the kU-structure via `Module.compHom e`.
  let k := ToType (TopCat.Presheaf.stalk O.obj x)
  let instCompHom : Module (restrictStalkRing X O x U hU)
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    Module.compHom (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) e.toRingHom
  -- AddEquiv from F_x to (t.ι →₀ k), transporting coefficients along `e`.
  let h : (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) ≃+ (t.ι →₀ k) :=
    g.toAddEquiv.trans (Finsupp.mapRange.addEquiv e.toAddEquiv)
  refine ⟨{ toFun := h
            invFun := h.symm
            left_inv := h.left_inv
            right_inv := h.right_inv
            map_add' := h.map_add
            map_smul' := ?_ }⟩
  intro c m
  change h (c • m) = c • h m
  -- The k-action on F_x restricts (along e) to the kU-action used by g.
  have hsmul : c • m = (e.symm c) • m := by
    have h1 : (e.symm c) • m = (e (e.symm c)) • m := rfl
    rw [h1, e.apply_symm_apply]
  have hg : g ((e.symm c) • m) = (e.symm c) • g m := g.map_smul (e.symm c) m
  rw [hsmul]
  change Finsupp.mapRange.addEquiv e.toAddEquiv (g.toAddEquiv ((e.symm c) • m)) = c • _
  have hgg : g.toAddEquiv (e.symm c • m) = e.symm c • g m := hg
  rw [hgg]
  ext i
  change (Finsupp.mapRange.addEquiv e.toAddEquiv (e.symm c • g m)) i
      = (c • Finsupp.mapRange.addEquiv e.toAddEquiv (g m)) i
  have he : ∀ y : restrictStalkRing X O x U hU, (e.toAddEquiv y) = e y := fun _ => rfl
  simp only [Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul, he, map_mul, e.apply_symm_apply]

/-- **Well-definedness of the rank (crux).**  Any two trivialisations of `F` whose open
domains both contain the point `x` have the same rank.  This is the invariant-basis-number
argument carried out on the stalk `F_x`, which is a free `O_{X,x}`-module on each
trivialisation's index set; over the nonzero commutative ring `O_{X,x}` the cardinality of a
free basis is an invariant. -/
@[ega "0 5.4.1" "partial", sga "6 I 6.10" "special case"]
theorem Trivialization.rank_eq_of_mem
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (hO : StalksNontrivial X O)
    (F : SheafOfModules.{u} (toRingSheaf X O))
    (x : X) {U V : Opens X} (hU : x ∈ U) (hV : x ∈ V)
    (t : Trivialization X (toRingSheaf X O) F U)
    (s : Trivialization X (toRingSheaf X O) F V) :
    t.rank = s.rank := by
  -- Let `k := O_{X,x}`, a nonzero commutative ring (`hO x` + the `CommRingCat` stalk).
  -- `et : Fx ≃ₗ[k] (t.ι →₀ k)` and `es : Fx ≃ₗ[k] (s.ι →₀ k)` from the crux helper_01c9.
  -- Then `es.symm.trans et : (s.ι →₀ k) ≃ₗ[k] (t.ι →₀ k)`; over the nonzero comm ring `k`
  -- (`StrongRankCondition` via `commRing_strongRankCondition`) `LinearEquiv.rank_eq` +
  -- `rank_finsupp_self` give `Cardinal.mk s.ι = Cardinal.mk t.ι`.
  -- SANITY CHECK PASSED  (lean-sanity-check found no counterexample; `hO` confirmed
  -- necessary — over the zero ring free modules of all ranks are isomorphic — and present.)
  classical
  obtain ⟨et⟩ := Trivialization.stalk_linearEquiv_finsupp X O F x hU t
  obtain ⟨es⟩ := Trivialization.stalk_linearEquiv_finsupp X O F x hV s
  -- `k = O_{X,x}` is a nonzero commutative ring, hence has the strong rank condition.
  have : Nontrivial (ToType (TopCat.Presheaf.stalk O.obj x)) := hO x
  have : StrongRankCondition (ToType (TopCat.Presheaf.stalk O.obj x)) :=
    commRing_strongRankCondition _
  -- The composite linear equivalence between the two finsupp free modules.
  have hrank : Module.rank (ToType (TopCat.Presheaf.stalk O.obj x))
      (s.ι →₀ ToType (TopCat.Presheaf.stalk O.obj x))
      = Module.rank (ToType (TopCat.Presheaf.stalk O.obj x))
        (t.ι →₀ ToType (TopCat.Presheaf.stalk O.obj x)) :=
    (es.symm.trans et).rank_eq
  -- `rank_finsupp_self` rewrites both ranks to the (lifted) cardinality of the index set.
  rw [rank_finsupp_self, rank_finsupp_self] at hrank
  -- In universe `u` the `Cardinal.lift` is the identity, so we recover `mk s.ι = mk t.ι`.
  simp only [Cardinal.lift_id] at hrank
  change Cardinal.mk t.ι = Cardinal.mk s.ι
  exact hrank.symm

/-- **Stacks Tag 01C9.**  Let `X` be a ringed space whose structure sheaf `O_X` is a sheaf
of commutative rings all of whose stalks `O_{X,x}` are nonzero, and let `F` be a locally
free sheaf of `O_X`-modules.  Then there is a locally constant function
`rank_F : X → Cardinal` such that for every point `x` and every trivialisation `t` of `F` on
an open neighbourhood `U` of `x`, the cardinality of the index set of `t` equals `rank_F x`.

This single statement encodes both that the rank at a point is well defined (independent of
the trivialisation chosen) and that the resulting function is locally constant. -/
@[stacks 01C9,
  ega "0 5.4.1" "n(x) locally constant",
  sga "6 I 6.0" "existence of rg_U(L)",
  ega "II 6.4.8" "partial",
  ega "IV 19.7.4" "partial",
  sga "5 VII 3.2" "more general",
  sga "6 I 6.10" "special case",
  sga "6 III 5.4.1" "special case"]
theorem exists_locallyConstant_rank
    (X : TopCat.{u})
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (hO : StalksNontrivial X O)
    (F : SheafOfModules.{u} (toRingSheaf X O))
    (hF : IsLocallyFree X (toRingSheaf X O) F) :
    ∃ rankF : X → Cardinal.{u},
      IsLocallyConstant rankF ∧
      ∀ (x : X) (U : Opens X), x ∈ U →
        ∀ t : Trivialization X (toRingSheaf X O) F U, t.rank = rankF x := by
  classical
  -- For each `x`, `hF x` provides an open neighbourhood and a trivialisation there.  Choose
  -- them: `Ux x` an open with `x ∈ Ux x`, and `tx x : Trivialization … (Ux x)`.
  set Ux : X → Opens X := fun x => (hF x).choose with hUx
  have hxUx : ∀ x, x ∈ Ux x := fun x => (hF x).choose_spec.1
  have hne : ∀ x, Nonempty (Trivialization X (toRingSheaf X O) F (Ux x)) :=
    fun x => (hF x).choose_spec.2
  set tx : ∀ x, Trivialization X (toRingSheaf X O) F (Ux x) := fun x => (hne x).some with htx
  -- Define the rank function as the rank of the chosen trivialisation at each point.
  refine ⟨fun x => (tx x).rank, ?_, ?_⟩
  · -- LOCAL CONSTANCY.  We show `rankF` is constant on each chosen neighbourhood `Ux x`.
    -- Via `IsLocallyConstant.iff_exists_open`: for each `x` exhibit the open `(Ux x : Set X)`
    -- containing `x` on which `rankF` is constant.  For `y ∈ Ux x`, both `tx x` (a
    -- trivialisation on `Ux x`, and `y ∈ Ux x`) and `tx y` (on `Ux y`, with `y ∈ Ux y`) are
    -- trivialisations whose domains contain `y`, so `Trivialization.rank_eq_of_mem` at `y`
    -- gives `(tx y).rank = (tx x).rank`, i.e. `rankF y = rankF x`.  This branch is fully
    -- discharged below using only `rank_eq_of_mem` (the single crux open goal).
    -- SANITY CHECK PASSED
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(Ux x : Set X), (Ux x).isOpen, hxUx x, ?_⟩
    intro y hy
    -- `tx y` on `Ux y ∋ y` and `tx x` on `Ux x ∋ y` (since `y ∈ Ux x`):
    exact Trivialization.rank_eq_of_mem X O hO F y (hxUx y) hy (tx y) (tx x)
  · -- MATCHING PROPERTY / WELL-DEFINEDNESS.  For any `x`, open `U ∋ x` and trivialisation
    -- `t` on `U`: apply `Trivialization.rank_eq_of_mem` at `x` to the pair `t` (on `U ∋ x`)
    -- and the chosen `tx x` (on `Ux x ∋ x`).  This gives `t.rank = (tx x).rank = rankF x`.
    -- SANITY CHECK PASSED
    intro x U hxU t
    exact Trivialization.rank_eq_of_mem X O hO F x hxU (hxUx x) t (tx x)

end LocallyFreeRank
