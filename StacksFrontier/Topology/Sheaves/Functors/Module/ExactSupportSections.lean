module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Functors.Module.SheafAdjunctionOverPushforward

/-!
# Closed quotient morphisms of ringed spaces, and descent of modules along them

A *closed quotient morphism of ringed spaces* is a morphism `i : Z ⟶ X` of ringed spaces whose
underlying continuous map is a homeomorphism onto a closed subset and whose comorphism of
structure sheaves `i^♯ : 𝒪_X ⟶ i_* 𝒪_Z` is surjective.  This is the situation of the Stacks
Project section on the right adjoint of pushforward for closed immersions.

The main content of this file is the *descent* functor for sheaves of modules.  Pushforward
of sheaves of modules along `i` factors as

`Mod(𝒪_Z) ⟶ Mod(i_* 𝒪_Z) ⟶ Mod(𝒪_X)`,

the second arrow being restriction of scalars along `i^♯`.  The first arrow,
`modulePushforwardPushedRing`, has a right adjoint `moduleDescend`, given on sections by
`V ↦ 𝓜(i_! V)` where `i_! V = X ∖ i(Z ∖ V)` is the largest open of `X` with inverse image `V`.
This is what allows an `i_* 𝒪_Z`-module on `X` to be read as an `𝒪_Z`-module on `Z`.

## Main definitions

* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces` packages the two ringed
  spaces, the morphism, and the closed-embedding and surjectivity hypotheses.
* `ClosedQuotientMorphismOfRingedSpaces.kernelIdeal` is the kernel ideal `ℐ = ker(i^♯)` on every
  open subset of the target.
* `ClosedQuotientMorphismOfRingedSpaces.opensFunctor` is `V ↦ X ∖ i(Z ∖ V)`, the right adjoint
  of `V ↦ i⁻¹ V`; it realises every open of `Z` as the inverse image of a *canonical* open of
  `X`.
* `ClosedQuotientMorphismOfRingedSpaces.pushedRingSheaf` is `i_* 𝒪_Z`, viewed as a sheaf of
  rings on `X`.
* `ClosedQuotientMorphismOfRingedSpaces.modulePushforwardPushedRing` and
  `ClosedQuotientMorphismOfRingedSpaces.moduleDescend` are the two functors between
  `Mod(𝒪_Z)` and `Mod(i_* 𝒪_Z)`.

## Main results

* `ClosedQuotientMorphismOfRingedSpaces.map_mem_kernelIdeal` records that restriction maps
  preserve the kernel ideals, so that `kernelIdeal` really is an ideal subsheaf of the
  structure sheaf.
* `ClosedQuotientMorphismOfRingedSpaces.eq_zero_of_opensMap_eq_bot`: an `i_* 𝒪_Z`-module
  vanishes on every open of `X` disjoint from the image of `Z`, because `i_* 𝒪_Z` is the zero
  ring there.
* `ClosedQuotientMorphismOfRingedSpaces.isSheaf_opensFunctor_op_comp`: restriction along
  `opensFunctor` takes a sheaf on `X` vanishing off the image of `Z` to a sheaf on `Z`.
* `ClosedQuotientMorphismOfRingedSpaces.moduleDescendAdjunction`:
  `modulePushforwardPushedRing ⊣ moduleDescend`.
* `ClosedQuotientMorphismOfRingedSpaces.modulePushforward_eq`: pushforward of modules along `i`
  is `modulePushforwardPushedRing` followed by restriction of scalars along `i^♯`.
* `ClosedQuotientMorphismOfRingedSpaces.moduleDescendCompPushforwardIso`: descent is a right
  inverse of `modulePushforwardPushedRing`.  This is a statement about `Mod(i_* 𝒪_Z)` only; it
  is *not* the essential-surjectivity half of Tag 08KS, which concerns `Mod(𝒪_X)`.  See the
  docstring of that declaration for what 08KS still needs.

## Implementation notes

A homeomorphism onto a closed subset is expressed by `Topology.IsClosedEmbedding`.
Surjectivity of a morphism of sheaves is local surjectivity, equivalently surjectivity on all
stalks.  The kernel ideal is represented sectionwise; naturality of the comorphism ensures that
restriction maps carry each such ideal into the corresponding ideal.

The functor `opensFunctor` is Mathlib's `Topology.IsInducing.functor`: an inducing map already
has a right adjoint on lattices of opens.  Note that `opensFunctor` is *not* a continuous
functor of sites — restriction along it takes the sheaf `𝒪_X` to a presheaf whose sections over
`⊥` are `𝒪_X(X ∖ i(Z))`, which need not be terminal — so the descent functor cannot be obtained
from `SheafOfModules.pushforwardPushforwardAdj`.  It is built by hand: the adjunction is
constructed on presheaves of modules, where no continuity is needed, and then restricted to
sheaves using that an `i_* 𝒪_Z`-module vanishes off the image of `Z`.

`pushedRingSheaf` is `pushOfRing` of Tag 008Z
(`StacksFrontier.Topology.Sheaves.Functors.Module.SheafAdjunctionOverPushforward`) at the
underlying continuous map of `i`, and `modulePushforwardPushedRing` agrees with that file's
`pushforwardModule` by `rfl` (`modulePushforwardPushedRing_eq`).  The latter is nonetheless
written out rather than defined as `pushforwardModule`, because `pushforwardModule` pins the
module universe to the space universe; defining it as
`SheafOfModules.pushforward (canonicalRingHom ..)` also inserts a
`ModuleCat.restrictScalars (𝟙 _)` layer that every downstream `rfl` has to unfold, which
exhausts the heartbeat budget of
`StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupport`.

Unlike `StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace`, the module universe here is
*not* tied to the space universe by `PresheafOfModules.instIsRightAdjointPushforward` — that
instance is only needed for `modulePullback`, which this file does not use.  Every module-level
declaration below is therefore stated at `max u v` for an independent `v`, which specialises to
the old `u` at `v := u`.  The module universe cannot be made entirely free: the sheaf condition
is manipulated through `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing` and
`TopCat.Sheaf.existsUnique_gluing'`, both of which assume `HasLimitsOfSize.{u, u}` on the
coefficient category for `X : TopCat.{u}`, and `AddCommGrpCat.{w}` has those limits only when
`UnivLE.{u, w}`.  So the module universe must dominate the space universe, which is what
`max u v` says.

## References

* [Stacks Project, Tag 0A74](https://stacks.math.columbia.edu/tag/0A74)
* [Stacks Project, Modules on Sites, Situation 17.6.1](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite Topology TopologicalSpace
open TopologicalSpace.Opens

universe v u

namespace RingedSpaceModuleAdjunction

/-- A morphism of ringed spaces which is a homeomorphism onto a closed subset and whose
comorphism of structure sheaves is surjective. -/
structure ClosedQuotientMorphismOfRingedSpaces where
  /-- The target ringed space. -/
  X : AlgebraicGeometry.RingedSpace.{u}
  /-- The source ringed space. -/
  Z : AlgebraicGeometry.RingedSpace.{u}
  /-- The morphism from the closed ringed subspace to the ambient ringed space. -/
  i : Z ⟶ X
  /-- The underlying continuous map is a homeomorphism onto a closed subset. -/
  isClosedEmbedding : Topology.IsClosedEmbedding
    (((AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).map i).base)
  /-- The comorphism `𝒪_X ⟶ i_* 𝒪_Z` is surjective as a morphism of sheaves. -/
  isLocallySurjective : TopCat.Presheaf.IsLocallySurjective
    (((AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).map i).c)

namespace ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-! ### The kernel ideal -/

/-- The ideal `ℐ ⊆ 𝒪_X` which is the kernel of the comorphism `𝒪_X ⟶ i_* 𝒪_Z`,
evaluated on an open subset of `X`. -/
noncomputable def kernelIdeal (U : Opens S.X) : Ideal (S.X.presheaf.obj (op U)) :=
  RingHom.ker
    (((AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).map S.i).c.app
      (op U)).hom

/-- Membership in the kernel ideal means being killed by the comorphism. -/
lemma mem_kernelIdeal_iff {U : Opens S.X} (x : S.X.presheaf.obj (op U)) :
    x ∈ S.kernelIdeal U ↔
      (((AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace
        (C := CommRingCat)).map S.i).c.app (op U)).hom x = 0 :=
  Iff.rfl

/-- The sectionwise kernels of the comorphism are compatible with restriction maps, so
`kernelIdeal` represents an ideal subsheaf of the structure sheaf. -/
lemma map_mem_kernelIdeal {U V : (Opens S.X)ᵒᵖ} (f : U ⟶ V) (x : S.X.presheaf.obj U)
    (hx : x ∈ S.kernelIdeal U.unop) :
    S.X.presheaf.map f x ∈ S.kernelIdeal V.unop := by
  set c := ((AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace
    (C := CommRingCat)).map S.i).c with hc
  have hx' : c.app U x = 0 := hx
  have h := NatTrans.naturality_apply c f x
  rw [hx', map_zero] at h
  exact h

/-! ### The right adjoint of `i⁻¹` on lattices of opens -/

/-- The underlying continuous map `Z ⟶ X` of a closed quotient morphism of ringed spaces. -/
noncomputable abbrev baseMap : S.Z.carrier ⟶ S.X.carrier :=
  ((AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).map S.i).base

/-- The underlying continuous map of a closed quotient morphism is inducing. -/
lemma isInducing_baseMap : IsInducing ⇑(ConcreteCategory.hom S.baseMap) :=
  S.isClosedEmbedding.isInducing

/-- `V ↦ X ∖ i(Z ∖ V)`, the largest open subset of `X` whose inverse image is `V`, as a functor
right adjoint to `U ↦ i⁻¹ U`. -/
noncomputable def opensFunctor : Opens S.Z ⥤ Opens S.X := S.isInducing_baseMap.functor

/-- `i⁻¹ ⊣ i_!` on lattices of open subsets. -/
noncomputable def opensAdjunction : opensMap S.i ⊣ S.opensFunctor :=
  S.isInducing_baseMap.adjunction

/-- The inverse image of `opensFunctor V` is `V` on the nose. -/
lemma opensMap_opensFunctor_obj (V : Opens S.Z) :
    (opensMap S.i).obj (S.opensFunctor.obj V) = V :=
  S.isInducing_baseMap.map_functorObj V

/-- The defining adjunction property of `opensFunctor`. -/
lemma le_opensFunctor_obj_iff {U : Opens S.X} {V : Opens S.Z} :
    U ≤ S.opensFunctor.obj V ↔ (opensMap S.i).obj U ≤ V :=
  S.isInducing_baseMap.le_functorObj_iff

/-- A point of the image lies in `opensFunctor V` exactly when it comes from `V`. -/
lemma baseMap_mem_opensFunctor_obj_iff (V : Opens S.Z) (z : S.Z.carrier) :
    ConcreteCategory.hom S.baseMap z ∈ S.opensFunctor.obj V ↔ z ∈ V :=
  S.isInducing_baseMap.mem_functorObj_iff V

/-- `opensFunctor` preserves binary intersections, being a right adjoint. -/
lemma opensFunctor_obj_inf (V V' : Opens S.Z) :
    S.opensFunctor.obj (V ⊓ V') = S.opensFunctor.obj V ⊓ S.opensFunctor.obj V' := by
  refine le_antisymm (le_inf (S.opensFunctor.map (homOfLE inf_le_left)).le
      (S.opensFunctor.map (homOfLE inf_le_right)).le) (S.le_opensFunctor_obj_iff.2 ?_)
  exact le_inf (le_trans (fun x hx => hx.1) (S.opensMap_opensFunctor_obj V).le)
    (le_trans (fun x hx => hx.2) (S.opensMap_opensFunctor_obj V').le)

/-- The complement of the image of `Z`, an open subset of `X` because `i` is closed. -/
noncomputable def opensComplRange : Opens S.X :=
  ⟨(Set.range ⇑(ConcreteCategory.hom S.baseMap))ᶜ,
    S.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The complement of the image of `Z` has empty inverse image, hence lies in
`opensFunctor ⊥`. -/
lemma opensComplRange_le_opensFunctor_bot : S.opensComplRange ≤ S.opensFunctor.obj ⊥ :=
  S.le_opensFunctor_obj_iff.2 fun z hz => absurd (Set.mem_range_self z) hz

/-- The inverse image of the complement of the image of `Z` is empty. -/
lemma opensMap_opensComplRange : (opensMap S.i).obj S.opensComplRange = ⊥ :=
  le_bot_iff.1 (S.le_opensFunctor_obj_iff.1 S.opensComplRange_le_opensFunctor_bot)

/-- The largest open with inverse image `i⁻¹ U` differs from `U` only away from the image of
`Z`. -/
lemma opensFunctor_opensMap_le_sup (U : Opens S.X) :
    S.opensFunctor.obj ((opensMap S.i).obj U) ≤
      U ⊔ (S.opensFunctor.obj ((opensMap S.i).obj U) ⊓ S.opensComplRange) := by
  intro x hx
  by_cases hr : x ∈ Set.range ⇑(ConcreteCategory.hom S.baseMap)
  · obtain ⟨z, rfl⟩ := hr
    exact Or.inl ((S.baseMap_mem_opensFunctor_obj_iff _ _).1 hx)
  · exact Or.inr ⟨hx, hr⟩

/-- `opensFunctor` turns a supremum into a supremum, up to the part of `X` off the image. -/
lemma opensFunctor_obj_iSup_le {ι : Type u} (U : ι → Opens S.Z) :
    S.opensFunctor.obj (iSup U) ≤ S.opensFunctor.obj ⊥ ⊔ ⨆ i, S.opensFunctor.obj (U i) := by
  intro x hx
  by_cases hr : x ∈ Set.range ⇑(ConcreteCategory.hom S.baseMap)
  · obtain ⟨z, rfl⟩ := hr
    rw [S.baseMap_mem_opensFunctor_obj_iff] at hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
    exact Or.inr (Opens.mem_iSup.2 ⟨i, (S.baseMap_mem_opensFunctor_obj_iff _ _).2 hi⟩)
  · exact Or.inl (S.opensComplRange_le_opensFunctor_bot hr)

/-! ### The pushed forward structure sheaf -/

/-- The sheaf of rings `i_* 𝒪_Z` on `X`, in the form consumed by `SheafOfModules`.

This is `pushOfRing` of Tag 008Z at the underlying continuous map of `i`. -/
noncomputable def pushedRingSheaf :
    Sheaf (Opens.grothendieckTopology S.X.carrier) RingCat.{u} :=
  pushOfRing S.baseMap (structureSheafRing S.Z)

/-- The comorphism of a closed quotient morphism, as a map `𝒪_X ⟶ i_* 𝒪_Z`. -/
noncomputable abbrev pushedRingHom : structureSheafRing S.X ⟶ S.pushedRingSheaf :=
  structureSheafHom S.i

/-- The sections of the structure sheaf of `Z` over the empty open subset form the zero ring. -/
lemma subsingleton_ringSheaf_bot : Subsingleton (S.Z.presheaf.obj (op (⊥ : Opens S.Z))) :=
  CommRingCat.subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty S.Z.sheaf)

/-- `i_* 𝒪_Z` is the zero ring on every open subset of `X` disjoint from the image of `Z`. -/
lemma subsingleton_pushedRingSheaf_obj (W : Opens S.X) (hW : (opensMap S.i).obj W = ⊥) :
    Subsingleton (S.pushedRingSheaf.obj.obj (op W)) := by
  have h : S.pushedRingSheaf.obj.obj (op W) =
      (structureSheafRing S.Z).obj.obj (op ((opensMap S.i).obj W)) := rfl
  rw [h, hW]
  exact S.subsingleton_ringSheaf_bot

/-- An `i_* 𝒪_Z`-module vanishes on every open subset of `X` disjoint from the image of `Z`:
there `1 = 0` in the ring of scalars. -/
lemma eq_zero_of_opensMap_eq_bot (M : PresheafOfModules.{max u v} S.pushedRingSheaf.obj)
    (W : Opens S.X) (hW : (opensMap S.i).obj W = ⊥) (m : M.obj (op W)) : m = 0 := by
  calc m = (1 : S.pushedRingSheaf.obj.obj (op W)) • m := (one_smul _ _).symm
    _ = (0 : S.pushedRingSheaf.obj.obj (op W)) • m := by
      rw [(S.subsingleton_pushedRingSheaf_obj W hW).elim 1 0]
    _ = 0 := zero_smul _ _

/-- An `i_* 𝒪_Z`-module vanishes on every open subset of the complement of the image of `Z`. -/
lemma eq_zero_of_le_opensComplRange (M : PresheafOfModules.{max u v} S.pushedRingSheaf.obj)
    (W : Opens S.X) (hW : W ≤ S.opensComplRange) (m : M.obj (op W)) : m = 0 := by
  exact S.eq_zero_of_opensMap_eq_bot M W
    (eq_bot_mono ((opensMap S.i).monotone hW) S.opensMap_opensComplRange) m

/-! ### Restriction along `opensFunctor` preserves the sheaf condition -/

/-- Restriction maps of a presheaf on a space whose opens form a poset do not depend on the
chosen inclusion. -/
lemma map_eq_map {T : TopCat.{u}} (P : TopCat.Presheaf AddCommGrpCat.{max u v} T)
    {A B : (Opens T)ᵒᵖ} (f g : A ⟶ B) (x : ToType (P.obj A)) : P.map f x = P.map g x := by
  rw [Subsingleton.elim f g]

/-- If a presheaf vanishes on opens with empty inverse image, any two of its sections over an open
contained in such an open are equal. -/
private lemma eq_of_le_of_opensMap_eq_bot
    {P : TopCat.Presheaf AddCommGrpCat.{max u v} S.X.carrier}
    (hvan : ∀ W : Opens S.X, (opensMap S.i).obj W = ⊥ → ∀ x : ToType (P.obj (op W)), x = 0)
    {W W' : Opens S.X} (hW : (opensMap S.i).obj W = ⊥) (h : W' ≤ W)
    (x y : ToType (P.obj (op W'))) : x = y :=
  (hvan W' (eq_bot_mono ((opensMap S.i).monotone h) hW) x).trans
    (hvan W' (eq_bot_mono ((opensMap S.i).monotone h) hW) y).symm

/-- Restriction along `opensFunctor` takes a sheaf on `X` which vanishes on every open subset
disjoint from the image of `Z` to a sheaf on `Z`.

Although `opensFunctor` does not preserve covers — the empty cover of `⊥` goes to the empty
cover of `X ∖ i(Z)` — it does so after the open `X ∖ i(Z)` is added to the family, and the
vanishing hypothesis makes the section over that extra open unique. -/
lemma isSheaf_opensFunctor_op_comp
    {P : TopCat.Presheaf AddCommGrpCat.{max u v} S.X.carrier} (hP : P.IsSheaf)
    (hvan : ∀ W : Opens S.X, (opensMap S.i).obj W = ⊥ → ∀ x : ToType (P.obj (op W)), x = 0) :
    TopCat.Presheaf.IsSheaf (X := S.Z.carrier) (S.opensFunctor.op ⋙ P) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  let W : Option ι → Opens S.X := fun j =>
    match j with
    | none => S.opensFunctor.obj ⊥
    | some i => S.opensFunctor.obj (U i)
  have hWbot : (opensMap S.i).obj (W none) = ⊥ := S.opensMap_opensFunctor_obj ⊥
  have hsub : ∀ {W' : Opens S.X}, W' ≤ W none → ∀ x y : ToType (P.obj (op W')), x = y :=
    fun h => eq_of_le_of_opensMap_eq_bot S hvan hWbot h
  have hWle : ∀ j, W j ≤ S.opensFunctor.obj (iSup U) := by
    rintro (_ | i)
    · exact (S.opensFunctor.map (homOfLE bot_le)).le
    · exact (S.opensFunctor.map (homOfLE (le_iSup U i))).le
  have hcover : S.opensFunctor.obj (iSup U) ≤ iSup W :=
    le_trans (S.opensFunctor_obj_iSup_le U)
      (sup_le (le_iSup W none) (iSup_le fun i => le_iSup W (some i)))
  let tf : ∀ j, ToType (P.obj (op (W j))) := fun j =>
    match j with
    | none => 0
    | some i => sf i
  have hcompat : TopCat.Presheaf.IsCompatible P W tf := by
    rintro (_ | i) (_ | i')
    · exact hsub (infLELeft _ _).le _ _
    · exact hsub (infLELeft _ _).le _ _
    · exact hsub (infLERight _ _).le _ _
    · have e : S.opensFunctor.obj (U i ⊓ U i') = W (some i) ⊓ W (some i') :=
        S.opensFunctor_obj_inf _ _
      have h := congrArg (fun x => P.map (eqToHom (congrArg op e)) x) (hsf i i')
      simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at h
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← P.map_comp, ← P.map_comp] at h
      exact (map_eq_map P _ _ _).trans (h.trans (map_eq_map P _ _ _))
  obtain ⟨s, hs, huniq⟩ :=
    TopCat.Sheaf.existsUnique_gluing' (⟨P, hP⟩ : TopCat.Sheaf _ _) W
      (S.opensFunctor.obj (iSup U)) (fun j => homOfLE (hWle j)) hcover tf hcompat
  refine ⟨s, fun i => ?_, fun y hy => huniq y ?_⟩
  · change P.map (S.opensFunctor.map (leSupr U i)).op s = sf i
    exact (map_eq_map P _ (homOfLE (hWle (some i))).op s).trans (hs (some i))
  · rintro (_ | i)
    · exact hsub le_rfl _ _
    · exact (map_eq_map P _ (S.opensFunctor.map (leSupr U i)).op y).trans (hy i)

/-! ### Descent of modules along a closed quotient morphism -/

/-- Restriction maps of a presheaf of modules on a space whose opens form a poset do not depend
on the chosen inclusion. -/
private lemma pmMap_eq {T : TopCat.{u}} {R : (Opens T)ᵒᵖ ⥤ RingCat.{u}}
    (N : PresheafOfModules.{max u v} R) {A B : (Opens T)ᵒᵖ} (f g : A ⟶ B) (x : N.obj A) :
    N.map f x = N.map g x :=
  N.congr_map_apply (Subsingleton.elim f g) x

/-- An endomorphism restriction map of a presheaf of rings on a poset of opens is the
identity. -/
private lemma ringMap_eq_id {T : TopCat.{u}} (R : (Opens T)ᵒᵖ ⥤ RingCat.{u}) {A : (Opens T)ᵒᵖ}
    (f : A ⟶ A) (x : R.obj A) : R.map f x = x := by
  rw [Subsingleton.elim f (𝟙 A), R.map_id]; rfl

/-- Two successive restriction maps of a presheaf of rings on a poset of opens returning to the
starting open compose to the identity. -/
private lemma ringMap_comp_eq_self {T : TopCat.{u}} (R : (Opens T)ᵒᵖ ⥤ RingCat.{u})
    {A B : (Opens T)ᵒᵖ} (f : A ⟶ B) (g : B ⟶ A) (x : R.obj A) : R.map g (R.map f x) = x := by
  rw [← ConcreteCategory.comp_apply, ← R.map_comp]
  exact ringMap_eq_id R _ x

/-- The identity restriction map of a presheaf of modules is the identity. -/
private lemma pmMap_id {T : TopCat.{u}} {R : (Opens T)ᵒᵖ ⥤ RingCat.{u}}
    (N : PresheafOfModules.{max u v} R) {A : (Opens T)ᵒᵖ} (x : N.obj A) : N.map (𝟙 A) x = x := by
  rw [N.map_id]; rfl

/-- Two successive restriction maps of a presheaf of modules on a poset of opens compose to the
unique restriction map between the end points. -/
private lemma pmMap_comp_eq {T : TopCat.{u}} {R : (Opens T)ᵒᵖ ⥤ RingCat.{u}}
    (N : PresheafOfModules.{max u v} R) {A B C D : (Opens T)ᵒᵖ} (f : A ⟶ B) (g : B ⟶ C)
    (f' : A ⟶ D) (g' : D ⟶ C) (x : N.obj A) : N.map g (N.map f x) = N.map g' (N.map f' x) := by
  rw [← N.map_comp_apply, ← N.map_comp_apply]
  exact pmMap_eq N _ _ x

/-- Two successive restriction maps of a presheaf of modules returning to the starting open
compose to the identity. -/
private lemma pmMap_comp_eq_self {T : TopCat.{u}} {R : (Opens T)ᵒᵖ ⥤ RingCat.{u}}
    (N : PresheafOfModules.{max u v} R) {A B : (Opens T)ᵒᵖ} (f : A ⟶ B) (g : B ⟶ A) (x : N.obj A) :
    N.map g (N.map f x) = x := by
  rw [← N.map_comp_apply, pmMap_eq N _ (𝟙 _) x, pmMap_id N x]

/-- The comparison `𝒪_Z ⟶ (i_* 𝒪_Z) ∘ i_!` of sheaves of rings on `Z`, induced by the counit
`i⁻¹ i_! ⟶ 𝟭`.  It is the ring datum along which descent restricts scalars. -/
noncomputable def descendRingHom :
    (structureSheafRing S.Z).obj ⟶ S.opensFunctor.op ⋙ S.pushedRingSheaf.obj :=
  Functor.whiskerRight (NatTrans.op S.opensAdjunction.counit) (structureSheafRing S.Z).obj

/-- `descendRingHom` is restriction along the counit of `i⁻¹ ⊣ i_!`. -/
lemma descendRingHom_app (V : (Opens S.Z)ᵒᵖ) :
    S.descendRingHom.app V =
      (structureSheafRing S.Z).obj.map (S.opensAdjunction.counit.app V.unop).op :=
  rfl

/-- Pushing a section of `i_* 𝒪_Z` forward and back along the adjunction `i⁻¹ ⊣ i_!` changes
nothing. -/
lemma pushedRingSheaf_map_descendRingHom_app (U : Opens S.X)
    (a : S.pushedRingSheaf.obj.obj (op U)) :
    S.pushedRingSheaf.obj.map (S.opensAdjunction.unit.app U).op
        (S.descendRingHom.app (op ((opensMap S.i).obj U)) a) = a := by
  rw [descendRingHom_app]
  exact ringMap_comp_eq_self (structureSheafRing S.Z).obj _ _ a

/-- Transporting a scalar from `Z` to `X` along the descent comparison and restricting back to
`U` recovers the original action. -/
lemma descend_smul_aux (M : PresheafOfModules.{max u v} S.pushedRingSheaf.obj) (U : Opens S.X)
    (r : S.pushedRingSheaf.obj.obj (op U))
    (y : M.obj (op (S.opensFunctor.obj ((opensMap S.i).obj U)))) :
    M.map (S.opensAdjunction.unit.app U).op
        (S.descendRingHom.app (op ((opensMap S.i).obj U)) r • y) =
      r • M.map (S.opensAdjunction.unit.app U).op y := by
  rw [PresheafOfModules.map_smul, S.pushedRingSheaf_map_descendRingHom_app U r]

/-- Pushforward of presheaves of modules from `Z` to `X`, with `i_* 𝒪_Z` as ring of scalars. -/
noncomputable def pushPresheaf :
    PresheafOfModules.{max u v} (structureSheafRing S.Z).obj ⥤
      PresheafOfModules.{max u v} S.pushedRingSheaf.obj :=
  PresheafOfModules.pushforward₀ (opensMap S.i) (structureSheafRing S.Z).obj

/-- Descent of presheaves of modules from `X` to `Z`: `V ↦ 𝓜(i_! V)`. -/
noncomputable def descendPresheaf :
    PresheafOfModules.{max u v} S.pushedRingSheaf.obj ⥤
      PresheafOfModules.{max u v} (structureSheafRing S.Z).obj :=
  PresheafOfModules.pushforward S.descendRingHom

/-- The underlying presheaf of a descended presheaf of modules is restriction along `i_!`. -/
lemma descendPresheaf_obj_presheaf (M : PresheafOfModules.{max u v} S.pushedRingSheaf.obj) :
    (S.descendPresheaf.obj M).presheaf = S.opensFunctor.op ⋙ M.presheaf :=
  rfl

/-- The hom-set bijection of the descent adjunction, from pushforward to descent. -/
noncomputable def descendHomEquivToFun
    {N : PresheafOfModules.{max u v} (structureSheafRing S.Z).obj}
    {M : PresheafOfModules.{max u v} S.pushedRingSheaf.obj} (f : S.pushPresheaf.obj N ⟶ M) :
    N ⟶ S.descendPresheaf.obj M where
  app V := N.map (S.opensAdjunction.counit.app V.unop).op ≫
    (ModuleCat.restrictScalars (S.descendRingHom.app V).hom).map
      (f.app (op (S.opensFunctor.obj V.unop)))
  naturality {V V'} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have key : N.map (S.opensAdjunction.counit.app V'.unop).op (N.map g x) =
        (S.pushPresheaf.obj N).map (S.opensFunctor.map g.unop).op
          (N.map (S.opensAdjunction.counit.app V.unop).op x) := by
      change _ = N.map ((opensMap S.i).map (S.opensFunctor.map g.unop)).op _
      exact pmMap_comp_eq N _ _ _ _ x
    change f.app (op (S.opensFunctor.obj V'.unop))
      (N.map (S.opensAdjunction.counit.app V'.unop).op (N.map g x)) = _
    rw [key]
    exact PresheafOfModules.naturality_apply f (S.opensFunctor.map g.unop).op _

/-- The hom-set bijection of the descent adjunction, from descent to pushforward. -/
noncomputable def descendHomEquivInvFun
    {N : PresheafOfModules.{max u v} (structureSheafRing S.Z).obj}
    {M : PresheafOfModules.{max u v} S.pushedRingSheaf.obj} (g : N ⟶ S.descendPresheaf.obj M) :
    S.pushPresheaf.obj N ⟶ M :=
  PresheafOfModules.homMk
    { app := fun U =>
        ((PresheafOfModules.toPresheaf (structureSheafRing S.Z).obj).map g).app
            (op ((opensMap S.i).obj U.unop)) ≫
          M.presheaf.map (S.opensAdjunction.unit.app U.unop).op
      naturality := by
        intro U U' k
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro n
        have hg := PresheafOfModules.naturality_apply g ((opensMap S.i).map k.unop).op n
        change M.map (S.opensAdjunction.unit.app U'.unop).op
            (g.app (op ((opensMap S.i).obj U'.unop))
              (N.map ((opensMap S.i).map k.unop).op n)) =
          M.map k (M.map (S.opensAdjunction.unit.app U.unop).op
            (g.app (op ((opensMap S.i).obj U.unop)) n))
        rw [hg]
        exact pmMap_comp_eq M _ _ _ _ _ }
    (by
      intro U r m
      let A : (Opens S.Z)ᵒᵖ := op ((opensMap S.i).obj U.unop)
      let r' : (structureSheafRing S.Z).obj.obj A := r
      let m' : N.obj A := m
      change M.map (S.opensAdjunction.unit.app U.unop).op (g.app A (r' • m')) =
        r • M.map (S.opensAdjunction.unit.app U.unop).op (g.app A m')
      rw [map_smul]
      exact S.descend_smul_aux M U.unop r (g.app A m'))

/-- Sections of the morphism produced by `descendHomEquivInvFun`. -/
lemma descendHomEquivInvFun_app_apply
    {N : PresheafOfModules.{max u v} (structureSheafRing S.Z).obj}
    {M : PresheafOfModules.{max u v} S.pushedRingSheaf.obj} (g : N ⟶ S.descendPresheaf.obj M)
    (U : (Opens S.X)ᵒᵖ) (n : (S.pushPresheaf.obj N).obj U) :
    (S.descendHomEquivInvFun g).app U n =
      M.map (S.opensAdjunction.unit.app U.unop).op
        (g.app (op ((opensMap S.i).obj U.unop)) n) :=
  rfl

/-- **Descent along a closed quotient morphism.** Pushforward of sheaves of modules from `Z` to
`X`, taken over the ring `i_* 𝒪_Z`, is left adjoint to `V ↦ 𝓜(i_! V)`. -/
noncomputable def descendPresheafAdjunction : S.pushPresheaf ⊣ S.descendPresheaf :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun N M =>
        { toFun := S.descendHomEquivToFun
          invFun := S.descendHomEquivInvFun
          left_inv := fun f => by
            refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun n => ?_)
            have hn := PresheafOfModules.naturality_apply f (S.opensAdjunction.unit.app U.unop).op
              (N.map (S.opensAdjunction.counit.app ((opensMap S.i).obj U.unop)).op n)
            change M.map (S.opensAdjunction.unit.app U.unop).op
                (f.app (op ((opensMap S.i ⋙ S.opensFunctor).obj U.unop))
                  (N.map (S.opensAdjunction.counit.app ((opensMap S.i).obj U.unop)).op n)) =
              f.app U n
            rw [← hn]
            change f.app U (N.map ((opensMap S.i).map (S.opensAdjunction.unit.app U.unop)).op
              (N.map (S.opensAdjunction.counit.app ((opensMap S.i).obj U.unop)).op n)) = _
            rw [pmMap_comp_eq_self N _ _ n]
          right_inv := fun g => by
            refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
            have hg := PresheafOfModules.naturality_apply g
              (S.opensAdjunction.counit.app V.unop).op x
            change M.map (S.opensAdjunction.unit.app (S.opensFunctor.obj V.unop)).op
                (g.app (op ((S.opensFunctor ⋙ opensMap S.i).obj V.unop))
                  (N.map (S.opensAdjunction.counit.app V.unop).op x)) = g.app V x
            rw [hg]
            exact pmMap_comp_eq_self M _ _ _ }
      homEquiv_naturality_left_symm := by
        intro N' N M u g
        refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun n => ?_)
        rfl
      homEquiv_naturality_right := by
        intro N M M' f v
        refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        rfl }

/-! ### The descent adjunction on sheaves of modules -/

/-- Pushforward of sheaves of modules from `Z` to `X`, with `i_* 𝒪_Z` as ring of scalars.

This is `pushforwardModule` of Tag 008Z at the underlying continuous map of `i` — see
`modulePushforwardPushedRing_eq` — spelled out only for the two reasons recorded in the
implementation notes of this file: `pushforwardModule` pins the module universe to the space
universe, and its unfolding carries a `ModuleCat.restrictScalars (𝟙 _)` layer that makes the
downstream `rfl`s in `StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupport` time out. -/
noncomputable def modulePushforwardPushedRing :
    SheafOfModules.{max u v} (structureSheafRing S.Z) ⥤
      SheafOfModules.{max u v} S.pushedRingSheaf where
  obj N :=
    { val := S.pushPresheaf.obj N.val
      isSheaf := ((((opensMap S.i).sheafPushforwardContinuous AddCommGrpCat.{max u v}
        (Opens.grothendieckTopology S.X.carrier)
        (Opens.grothendieckTopology S.Z.carrier))).obj ⟨_, N.isSheaf⟩).property }
  map f := { val := S.pushPresheaf.map f.val }

/-- At the module universe of the underlying space, `modulePushforwardPushedRing` is Tag 008Z's
`pushforwardModule`. -/
lemma modulePushforwardPushedRing_eq :
    S.modulePushforwardPushedRing = pushforwardModule S.baseMap (structureSheafRing S.Z) :=
  rfl

/-- **Descent of sheaves of modules.** An `i_* 𝒪_Z`-module on `X` read as an `𝒪_Z`-module on
`Z`: its sections over `V` are the sections over the largest open `i_! V` of `X` with inverse
image `V`. -/
noncomputable def moduleDescend :
    SheafOfModules.{max u v} S.pushedRingSheaf ⥤
      SheafOfModules.{max u v} (structureSheafRing S.Z) where
  obj M :=
    { val := S.descendPresheaf.obj M.val
      isSheaf := S.isSheaf_opensFunctor_op_comp M.isSheaf
        fun W hW x => S.eq_zero_of_opensMap_eq_bot M.val W hW x }
  map f := { val := S.descendPresheaf.map f.val }

/-- Pushforward of sheaves of modules from `Z` to `X`, taken over the ring `i_* 𝒪_Z`, is left
adjoint to descent.

This is an adjunction over `i_* 𝒪_Z`, not over `𝒪_X`: it says nothing yet about
`modulePushforward S.i`, which is this functor followed by
`SheafOfModules.restrictScalars (structureSheafHom S.i)`. -/
noncomputable def moduleDescendAdjunction :
    S.modulePushforwardPushedRing ⊣ S.moduleDescend :=
  Adjunction.restrictFullyFaithful S.descendPresheafAdjunction
    (SheafOfModules.fullyFaithfulForget (structureSheafRing S.Z))
    (SheafOfModules.fullyFaithfulForget S.pushedRingSheaf)
    (Iso.refl _) (Iso.refl _)

/-- Pushforward of sheaves of modules along `i` is pushforward over `i_* 𝒪_Z` followed by
restriction of scalars along the comorphism `i^♯`. -/
lemma modulePushforward_eq :
    modulePushforward S.i =
      S.modulePushforwardPushedRing ⋙ SheafOfModules.restrictScalars (structureSheafHom S.i) :=
  rfl

/-! ### Descent is inverse to pushforward over `i_* 𝒪_Z` -/

/-- The counit of the descent adjunction, at the level of presheaves of modules: restriction
from `i_! i⁻¹ U` to `U`. -/
noncomputable def descendCounitPresheaf (M : PresheafOfModules.{max u v} S.pushedRingSheaf.obj) :
    S.pushPresheaf.obj (S.descendPresheaf.obj M) ⟶ M :=
  S.descendHomEquivInvFun (𝟙 _)

/-- The counit of the descent adjunction is restriction along `U ≤ i_! i⁻¹ U`. -/
lemma descendCounitPresheaf_app_apply (M : PresheafOfModules.{max u v} S.pushedRingSheaf.obj)
    (U : (Opens S.X)ᵒᵖ)
    (m : M.obj (op (S.opensFunctor.obj ((opensMap S.i).obj U.unop)))) :
    (S.descendCounitPresheaf M).app U m = M.map (S.opensAdjunction.unit.app U.unop).op m :=
  rfl

/-- An `i_* 𝒪_Z`-module has the same sections over `U` as over the largest open `i_! i⁻¹ U`
with the same inverse image, because the difference of the two opens lies off the image of
`Z`, where the module vanishes. -/
lemma bijective_descendCounitPresheaf_app (M : SheafOfModules.{max u v} S.pushedRingSheaf)
    (U : (Opens S.X)ᵒᵖ) :
    Function.Bijective (ConcreteCategory.hom ((S.descendCounitPresheaf M.val).app U)) := by
  obtain ⟨U⟩ := U
  let F : TopCat.Sheaf AddCommGrpCat.{max u v} S.X.carrier := ⟨M.val.presheaf, M.isSheaf⟩
  let W : Opens S.X := S.opensFunctor.obj ((opensMap S.i).obj U)
  let B : Opens S.X := W ⊓ S.opensComplRange
  let Wf : Bool → Opens S.X := fun b => match b with | true => U | false => B
  have hWfle : ∀ b, Wf b ≤ W := by
    rintro (_ | _)
    · exact inf_le_left
    · exact (S.opensAdjunction.unit.app U).le
  have hcover : W ≤ iSup Wf :=
    le_trans (S.opensFunctor_opensMap_le_sup U)
      (sup_le (le_iSup Wf true) (le_iSup Wf false))
  have hzero : ∀ {W' : Opens S.X}, W' ≤ B → ∀ x y : ToType (F.1.obj (op W')), x = y :=
    fun h => eq_of_le_of_opensMap_eq_bot S (P := F.1)
      (fun W hW x => S.eq_zero_of_opensMap_eq_bot M.val W hW x) S.opensMap_opensComplRange
      (h.trans inf_le_right)
  let sf : ToType (F.1.obj (op U)) → ∀ b, ToType (F.1.obj (op (Wf b))) := fun m b =>
    match b with | true => m | false => 0
  have key : ∀ m : ToType (F.1.obj (op U)),
      ∃! s : ToType (F.1.obj (op W)), ∀ b, F.1.map (homOfLE (hWfle b)).op s = sf m b := by
    intro m
    refine TopCat.Sheaf.existsUnique_gluing' F Wf W (fun b => homOfLE (hWfle b)) hcover _ ?_
    rintro (_ | _) (_ | _)
    · exact hzero inf_le_left _ _
    · exact hzero inf_le_left _ _
    · exact hzero inf_le_right _ _
    · exact map_eq_map F.1 _ _ m
  have hres : ∀ (y : ToType (F.1.obj (op W))),
      F.1.map (homOfLE (hWfle true)).op y =
        ConcreteCategory.hom ((S.descendCounitPresheaf M.val).app (op U)) y :=
    fun y => map_eq_map F.1 _ (S.opensAdjunction.unit.app U).op y
  constructor
  · intro s s' hss'
    obtain ⟨t, -, huniq⟩ :=
      key (ConcreteCategory.hom ((S.descendCounitPresheaf M.val).app (op U)) s)
    have hspec : ∀ (y : ToType (F.1.obj (op W))),
        ConcreteCategory.hom ((S.descendCounitPresheaf M.val).app (op U)) y =
          ConcreteCategory.hom ((S.descendCounitPresheaf M.val).app (op U)) s →
        ∀ b, F.1.map (homOfLE (hWfle b)).op y =
          sf (ConcreteCategory.hom ((S.descendCounitPresheaf M.val).app (op U)) s) b := by
      rintro y hy (_ | _)
      · exact hzero le_rfl _ _
      · exact (hres y).trans hy
    exact (huniq s (hspec s rfl)).trans (huniq s' (hspec s' hss'.symm)).symm
  · intro m
    obtain ⟨s, hs, -⟩ := key m
    exact ⟨s, (hres s).symm.trans (hs true)⟩

/-- The counit of the descent adjunction is an isomorphism: descent followed by pushforward
over `i_* 𝒪_Z` is the identity. -/
noncomputable def descendCounitIso (M : SheafOfModules.{max u v} S.pushedRingSheaf) :
    S.pushPresheaf.obj (S.descendPresheaf.obj M.val) ≅ M.val :=
  haveI : ∀ U, IsIso ((S.descendCounitPresheaf M.val).app U) := fun U =>
    (ConcreteCategory.isIso_iff_bijective _).2 (S.bijective_descendCounitPresheaf_app M U)
  PresheafOfModules.isoMk (fun U => asIso ((S.descendCounitPresheaf M.val).app U))
    (fun {_ _} f => (S.descendCounitPresheaf M.val).naturality f)

/-- Descent is a right inverse of pushforward over `i_* 𝒪_Z` on sheaves of modules: the counit
of `moduleDescendAdjunction` is an isomorphism, so `modulePushforwardPushedRing` is essentially
surjective onto `Mod(i_* 𝒪_Z)`.

This is **not** yet the essential-surjectivity half of Tag 08KS, which is about
`modulePushforward S.i` and `Mod(𝒪_X)`.  Turning it into that statement needs
`SheafOfModules.restrictScalars (structureSheafHom S.i)` to be an equivalence from
`Mod(i_* 𝒪_Z)` onto the full subcategory of `𝒪_X`-modules killed by `kernelIdeal`, which is
where `ClosedQuotientMorphismOfRingedSpaces.isLocallySurjective` enters and is not done here.
For the full-faithfulness half of that comparison Mathlib already has
`PresheafOfModules.restrictHomEquivOfIsLocallySurjective`
(`Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean`); what remains for 08KS is to
identify the image of `restrictScalars` with the `kernelIdeal`-annihilated modules, in both
directions. -/
noncomputable def moduleDescendCompPushforwardIso :
    S.moduleDescend ⋙ S.modulePushforwardPushedRing ≅
      𝟭 (SheafOfModules.{max u v} S.pushedRingSheaf) :=
  NatIso.ofComponents
    (fun M => (SheafOfModules.fullyFaithfulForget S.pushedRingSheaf).preimageIso
      (S.descendCounitIso M))
    fun {M M'} f => by
      refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
      refine ModuleCat.hom_ext (LinearMap.ext fun n => ?_)
      change M'.val.map (S.opensAdjunction.unit.app U.unop).op
          (f.val.app (op ((opensMap S.i ⋙ S.opensFunctor).obj U.unop)) n) =
        f.val.app (op ((𝟭 (Opens S.X)).obj U.unop))
          (M.val.map (S.opensAdjunction.unit.app U.unop).op n)
      exact (PresheafOfModules.naturality_apply f.val
        (S.opensAdjunction.unit.app U.unop).op n).symm

end ClosedQuotientMorphismOfRingedSpaces

end RingedSpaceModuleAdjunction

end
