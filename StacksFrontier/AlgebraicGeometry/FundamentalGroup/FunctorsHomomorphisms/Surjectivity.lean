module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.Comparison
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute

/-!
# Surjectivity in the functoriality of Galois categories

For an exact functor between Galois categories, the induced homomorphism on automorphism groups
is surjective exactly when the functor is fully faithful. This is also equivalent to preservation
of connected objects, to lifting maps from a final object, and to bijectivity on maps out of final
objects.

## Main definitions

* `CategoryTheory.mapFromTerminal` is the canonical map on morphisms out of chosen final objects.
* `CategoryTheory.isTerminalObjOfExactFunctor` is the final object witness for the image of a
  final object under an exact functor.

## Main results

* `CategoryTheory.surjective_inducedHom_tfae_of_fiberIso` gives the five equivalent
  characterizations of surjectivity for the continuous homomorphism produced by a choice of
  fibre-functor isomorphism.
* `CategoryTheory.surjective_inducedHom_tfae` is the same equivalence for an arbitrary
  `CategoryTheory.GaloisFunctorData` over that isomorphism.

## Implementation notes

The final objects are supplied together with witnesses of their universal properties. The
canonical identification of the target's chosen final object with the image of the source's
chosen final object is made explicit, so that the fifth condition is literally the map between
the two hom-sets in the source; the witness that this image is final is *derived* from exactness
of the functor by `CategoryTheory.isTerminalObjOfExactFunctor`, and is not a hypothesis. The
functoriality square and its induced continuous homomorphism are represented by
`CategoryTheory.GaloisFunctorData`; the continuous homomorphism of the diagram is the one
produced from the fibre-functor isomorphism by `CategoryTheory.galoisFunctorDataOfFiberIso`, so
no part of the functoriality data is assumed.

## References

* [Stacks Project, Tag 0BN6](https://stacks.math.columbia.edu/tag/0BN6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

universe u v u' v' w
universe uG

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

/-- The canonical map on morphisms out of chosen final objects, using the unique isomorphism
between the target's chosen final object and the image of the source's chosen final object. -/
public def mapFromTerminal (H : C ⥤ C') {star : C} {star' : C'}
    (hstar' : IsTerminal star') (hHstar : IsTerminal (H.obj star)) (X : C) :
    (star ⟶ X) → (star' ⟶ H.obj X) :=
  fun f ↦ (hstar'.uniqueUpToIso hHstar).hom ≫ H.map f

/-- An exact functor preserves final objects: the image of a final object under a functor
preserving finite limits is again final. -/
@[sga "4 IV 4.3" "Necessity"]
public noncomputable def isTerminalObjOfExactFunctor (H : C ⥤ C')
    (hH : exactFunctor C C' H) {star : C} (hstar : IsTerminal star) :
    IsTerminal (H.obj star) := by
  have : PreservesFiniteLimits H := hH.1
  exact hstar.isTerminalObj H star

private theorem mapFromTerminal_bijective_of_fullyFaithful
    (H : C ⥤ C') {star : C} {star' : C'}
    (hstar' : IsTerminal star') (hHstar : IsTerminal (H.obj star))
    (hF : H.FullyFaithful) (X : C) :
    Function.Bijective (mapFromTerminal H hstar' hHstar X) := by
  let e := hstar'.uniqueUpToIso hHstar
  refine ⟨fun f g h ↦ hF.map_injective ((cancel_epi e.hom).mp h), fun g ↦ ?_⟩
  obtain ⟨f, hf⟩ := hF.map_surjective (e.inv ≫ g)
  refine ⟨f, ?_⟩
  show e.hom ≫ H.map f = g
  rw [hf, ← Category.assoc, e.hom_inv_id, Category.id_comp]

private theorem reflectsIsomorphisms_of_fiberIso
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) : H.ReflectsIsomorphisms := by
  have : F.ReflectsIsomorphisms := reflectsIsomorphisms_of_comp F FintypeCat.incl
  have : (H ⋙ F').ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_iso t.symm
  exact reflectsIsomorphisms_of_comp H F'

private theorem terminal_not_initial
    (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F')]
    {star' : C'} (hstar' : IsTerminal star') : IsInitial star' → False := by
  let G := setValuedFiberFunctor F'
  intro h0
  have h0' : IsInitial (G.obj star') := h0.isInitialObj G star'
  have h1' : IsTerminal (G.obj star') := hstar'.isTerminalObj G star'
  let : Unique (G.obj star') := Types.isTerminalEquivUnique _ h1'
  have : IsEmpty (G.obj star') := (Types.initial_iff_empty _).mp ⟨h0'⟩
  exact isEmptyElim (default : G.obj star')

/-- A connected object receiving a map from a final object is itself final. -/
private noncomputable def isTerminal_of_connected_of_hom
    (F : C ⥤ FintypeCat.{w}) [IsGaloisCategory (setValuedFiberFunctor F)]
    {star X : C} (hstar : IsTerminal star) (hX : PreGaloisCategory.IsConnected X)
    (g : star ⟶ X) : IsTerminal X := by
  have : Mono g := hstar.mono_from g
  have : IsIso g := hX.noTrivialComponent star g (terminal_not_initial F hstar)
  exact hstar.ofIso (asIso g)

private theorem lift_of_preserves_connected
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (t : H ⋙ F' ≅ F)
    {star : C} {star' : C'} (hstar : IsTerminal star) (hstar' : IsTerminal star')
    (hHstar : IsTerminal (H.obj star))
    (hc : ∀ X : C, PreGaloisCategory.IsConnected X →
      PreGaloisCategory.IsConnected (H.obj X))
    (X : C) (hX : PreGaloisCategory.IsConnected X)
    (f : Nonempty (star' ⟶ H.obj X)) : Nonempty (star ⟶ X) := by
  have : H.ReflectsIsomorphisms := reflectsIsomorphisms_of_fiberIso F F' H t
  obtain ⟨g⟩ := f
  have hHX : IsTerminal (H.obj X) := isTerminal_of_connected_of_hom F' hstar' (hc X hX) g
  let q : X ⟶ star := hstar.from X
  have : IsIso (H.map q) := isIso_of_isTerminal hHX hHstar _
  have : IsIso q := isIso_of_reflects_iso q H
  exact ⟨inv q⟩

private theorem full_contAction_res_of_surjective
    {G K : Type*} [Group G] [TopologicalSpace G] [Group K] [TopologicalSpace K]
    (f : G →ₜ* K) (hf : Function.Surjective f) :
    (ContAction.res FintypeCat f).Full := by
  constructor
  intro X Y g
  obtain ⟨q, hq⟩ := (Action.full_res FintypeCat f.toMonoidHom hf).map_surjective g.hom
  exact ⟨⟨q⟩, ObjectProperty.hom_ext _ hq⟩

private noncomputable def fullyFaithful_of_surjective_inducedHom
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    (H : C ⥤ C') (t : H ⋙ F' ≅ F)
    (d : GaloisFunctorData F F' H t)
    [(PreGaloisCategory.functorToContAction F).Full]
    [(PreGaloisCategory.functorToContAction F).Faithful]
    [(PreGaloisCategory.functorToContAction F').Faithful]
    (h : Function.Surjective d.hom) : H.FullyFaithful := by
  let A := PreGaloisCategory.functorToContAction F
  let B := PreGaloisCategory.functorToContAction F'
  haveI : (ContAction.res FintypeCat d.hom).Full :=
    full_contAction_res_of_surjective d.hom h
  haveI : (A ⋙ ContAction.res FintypeCat d.hom).Full := inferInstance
  haveI : (H ⋙ B).Full := Functor.Full.of_iso d.actionIso
  haveI : H.Full := Functor.Full.of_comp_faithful H B
  haveI : (ContAction.res FintypeCat d.hom).Faithful := ⟨fun heq ↦ ObjectProperty.hom_ext _
    ((Action.res FintypeCat d.hom.toMonoidHom).map_injective (congrArg (·.hom) heq))⟩
  haveI : (A ⋙ ContAction.res FintypeCat d.hom).Faithful := inferInstance
  haveI : (H ⋙ B).Faithful := Functor.Faithful.of_iso d.actionIso
  haveI : H.Faithful := Functor.Faithful.of_comp H B
  exact Functor.FullyFaithful.ofFullyFaithful H

private theorem preserves_connected_of_surjective_inducedHom
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (t : H ⋙ F' ≅ F)
    (d : GaloisFunctorData F F' H t)
    (h : Function.Surjective d.hom) (X : C)
    (hX : PreGaloisCategory.IsConnected X) :
    PreGaloisCategory.IsConnected (H.obj X) := by
  let : PreGaloisCategory C := preGalois_of_isGaloisCategory F
  let : PreGaloisCategory.FiberFunctor F := IsGaloisCategory.fiberFunctor F
  let : GaloisCategory C := IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F)
  let : PreGaloisCategory.IsConnected X := hX
  have : Nonempty (F'.obj (H.obj X)) := by
    obtain ⟨x⟩ : Nonempty (F.obj X) := inferInstance
    exact ⟨t.inv.app X x⟩
  have : MulAction.IsPretransitive (Aut F')
      (((PreGaloisCategory.functorToContAction F ⋙
        ContAction.res FintypeCat d.hom).obj X).obj.V) :=
    MulAction.isPretransitive_compHom (G := F.obj X)
      (f := d.hom.toMonoidHom) h
  let e : ((PreGaloisCategory.functorToContAction F ⋙
      ContAction.res FintypeCat d.hom).obj X).obj ≅
      ((H ⋙ PreGaloisCategory.functorToContAction F').obj X).obj :=
    (ObjectProperty.ι _).mapIso (d.actionIso.app X)
  have : MulAction.IsPretransitive (Aut F') (F'.obj (H.obj X)) :=
    pretransitive_of_actionIso e
  exact isConnected_of_fiber_pretransitive F' (H.obj X)

private theorem open_overgroup_of_not_surjective
    {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    [TotallyDisconnectedSpace K] (f : G →ₜ* K)
    (hf : ¬ Function.Surjective f) :
    ∃ U : OpenSubgroup K, (∀ g : G, f g ∈ U) ∧ U ≠ ⊤ := by
  obtain ⟨k, hk⟩ := not_forall.mp hf
  let L : ClosedSubgroup K :=
    { toSubgroup := f.range
      isClosed' := by
        show IsClosed (Set.range f.toContinuousMap)
        simpa only [Set.image_univ] using (isCompact_univ.image f.continuous).isClosed }
  have hEq := ProfiniteGrp.closedSubgroup_eq_sInf_open L
  have hkn : k ∉ L := hk
  have hkn' : k ∉ (sInf {N : Subgroup K | IsOpen (N : Set K) ∧ L ≤ N} : Subgroup K) := by
    rwa [← hEq]
  by_contra hnone
  apply hkn'
  apply Subgroup.mem_sInf.mpr
  intro N hN
  by_contra hknN
  let U : OpenSubgroup K := ⟨N, hN.1⟩
  have hr : ∀ g : G, f g ∈ U := fun g => hN.2 ⟨g, rfl⟩
  have hU : U ≠ ⊤ := by
    intro heq
    apply hknN
    show k ∈ (U : Subgroup K)
    rw [heq]
    trivial
  exact hnone ⟨U, hr, hU⟩

private theorem fixedPoint_to_morphism
    (F : C ⥤ FintypeCat.{w}) [GaloisCategory C]
    [PreGaloisCategory.FiberFunctor F]
    {S Y : C} [Unique (F.obj S)]
    (x : F.obj Y) (hx : ∀ g : Aut F, g • x = x) :
    Nonempty (S ⟶ Y) := by
  let p : (PreGaloisCategory.functorToAction F).obj S ⟶
      (PreGaloisCategory.functorToAction F).obj Y :=
    { hom := FintypeCat.homMk (fun _ => x)
      comm := by
        intro g
        ext y
        show x = g • x
        exact (hx g).symm }
  obtain ⟨f, hf⟩ := (PreGaloisCategory.functorToAction F).map_surjective p
  exact ⟨f⟩

private theorem fixed_of_actionHom {G : Type*} [Group G]
    {A B : Action FintypeCat.{w} G} (f : A ⟶ B)
    {x : A.V} (hx : ∀ g : G, g • x = x) :
    ∀ g : G, g • f.hom x = f.hom x := by
  intro g
  have h := ConcreteCategory.congr_hom (f.comm g) x
  change f.hom (g • x) = g • f.hom x at h
  rw [hx g] at h
  exact h.symm

private theorem surjective_of_lifting_connected
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (t : H ⋙ F' ≅ F)
    (d : GaloisFunctorData F F' H t)
    {star : C} {star' : C'} (hstar : IsTerminal star) (hstar' : IsTerminal star')
    (h : ∀ X : C, PreGaloisCategory.IsConnected X →
      Nonempty (star' ⟶ H.obj X) → Nonempty (star ⟶ X)) :
    Function.Surjective d.hom := by
  classical
  let : PreGaloisCategory C := preGalois_of_isGaloisCategory F
  let : PreGaloisCategory.FiberFunctor F := IsGaloisCategory.fiberFunctor F
  let : GaloisCategory C := IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F)
  let : PreGaloisCategory C' := preGalois_of_isGaloisCategory F'
  let : PreGaloisCategory.FiberFunctor F' := IsGaloisCategory.fiberFunctor F'
  let : GaloisCategory C' := IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F')
  by_contra hsurj
  obtain ⟨U, hU, hUproper⟩ := open_overgroup_of_not_surjective d.hom hsurj
  let Q : ContAction FintypeCat.{w} (Aut F) := quotientContActionSwitch U
  obtain ⟨X, ⟨e⟩⟩ :=
    Functor.EssSurj.mem_essImage (PreGaloisCategory.functorToContAction F) Q
  let E : (PreGaloisCategory.functorToAction F).obj X ≅ Q.obj :=
    (ObjectProperty.ι _).mapIso e
  let q : Q.obj.V :=
    (FintypeCat.uSwitchEquiv (quotientContAction U).obj.V).symm
      (⟦1⟧ : Aut F ⧸ U.toSubgroup)
  have : Nonempty (F.obj X) := ⟨E.inv.hom q⟩
  have : MulAction.IsPretransitive (Aut F) Q.obj.V := by
    have : MulAction.IsPretransitive (Aut F) (quotientContAction U).obj.V :=
      MulAction.isPretransitive_quotient (Aut F) U.toSubgroup
    exact pretransitive_uSwitch (A := (quotientContAction U).obj)
  have : MulAction.IsPretransitive (Aut F) (F.obj X) :=
    pretransitive_of_actionIso E.symm
  have hX : PreGaloisCategory.IsConnected X :=
    isConnected_of_fiber_pretransitive F X
  let x : F.obj X := E.inv.hom q
  have hx : ∀ g' : Aut F', d.hom g' • x = x := by
    intro g'
    have hc := ConcreteCategory.congr_hom (E.inv.comm (d.hom g')) q
    change E.inv.hom ((d.hom g') • q) = (d.hom g') • x at hc
    rw [fixed_quotientSwitch U (d.hom g') (hU g')] at hc
    exact hc.symm
  let D : ((PreGaloisCategory.functorToContAction F ⋙
      ContAction.res FintypeCat d.hom).obj X).obj ≅
      ((H ⋙ PreGaloisCategory.functorToContAction F').obj X).obj :=
    (ObjectProperty.ι _).mapIso (d.actionIso.app X)
  let y : F'.obj (H.obj X) := D.hom.hom x
  have hy : ∀ g' : Aut F', g' • y = y := fixed_of_actionHom D.hom hx
  let G' := setValuedFiberFunctor F'
  let : Unique (F'.obj star') :=
    Types.isTerminalEquivUnique _ (hstar'.isTerminalObj G' star')
  obtain ⟨f'⟩ := fixedPoint_to_morphism F' (S := star') (Y := H.obj X) y hy
  obtain ⟨f⟩ := h X hX ⟨f'⟩
  have hXt : IsTerminal X := isTerminal_of_connected_of_hom F hstar hX f
  let G := setValuedFiberFunctor F
  let : Unique (F.obj X) :=
    Types.isTerminalEquivUnique _ (hXt.isTerminalObj G X)
  have hEsurj : Function.Surjective E.hom.hom :=
    ((ConcreteCategory.isIso_iff_bijective E.hom.hom).mp inferInstance).2
  have : Subsingleton ((PreGaloisCategory.functorToAction F).obj X).V :=
    inferInstanceAs (Subsingleton (F.obj X))
  have hQ : Subsingleton Q.obj.V := hEsurj.subsingleton
  refine hUproper (top_unique fun g _ ↦ U.inv_mem_iff.mp ?_)
  have hqg : (⟦g⟧ : Aut F ⧸ U.toSubgroup) = ⟦1⟧ :=
    (FintypeCat.uSwitchEquiv (quotientContAction U).obj.V).symm.injective (hQ.elim _ _)
  simpa using QuotientGroup.eq.mp hqg

/-- The five characterizations of surjectivity of the homomorphism induced by an exact functor
between Galois categories. -/
@[stacks 0BN6, sga "1 V 6.9" "more general", sga "1 V 6.10" "a) <=> fully faithful"]
public theorem surjective_inducedHom_tfae
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (_hH : exactFunctor C C' H) (t : H ⋙ F' ≅ F)
    (d : GaloisFunctorData F F' H t)
    (star : C) (star' : C') (hstar : IsTerminal star) (hstar' : IsTerminal star')
    (hHstar : IsTerminal (H.obj star)) :
    List.TFAE
      [ Function.Surjective d.hom,
        Nonempty H.FullyFaithful,
        ∀ X : C, PreGaloisCategory.IsConnected X →
          PreGaloisCategory.IsConnected (H.obj X),
        ∀ X : C, PreGaloisCategory.IsConnected X →
          Nonempty (star' ⟶ H.obj X) → Nonempty (star ⟶ X),
        ∀ X : C, Function.Bijective (mapFromTerminal H hstar' hHstar X) ] := by
  classical
  let : PreGaloisCategory C := preGalois_of_isGaloisCategory F
  let : PreGaloisCategory.FiberFunctor F := IsGaloisCategory.fiberFunctor F
  let : GaloisCategory C := IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F)
  let : PreGaloisCategory C' := preGalois_of_isGaloisCategory F'
  let : PreGaloisCategory.FiberFunctor F' := IsGaloisCategory.fiberFunctor F'
  let : GaloisCategory C' := IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F')
  tfae_have 1 → 2 := fun hs =>
    ⟨fullyFaithful_of_surjective_inducedHom F F' H t d hs⟩
  tfae_have 2 → 5 := fun ⟨hff⟩ X =>
    mapFromTerminal_bijective_of_fullyFaithful H hstar' hHstar hff X
  tfae_have 5 → 4 := fun hh X _ ⟨f⟩ => ⟨((hh X).2 f).choose⟩
  tfae_have 4 → 1 :=
    surjective_of_lifting_connected F F' H t d hstar hstar'
  tfae_have 1 → 3 := fun hs X hX =>
    preserves_connected_of_surjective_inducedHom F F' H t d hs X hX
  tfae_have 3 → 4 := fun hc X hX hf =>
    lift_of_preserves_connected F F' H t hstar hstar' hHstar hc X hX hf
  tfae_finish

/-- The five characterizations of surjectivity of the homomorphism induced by an exact functor
between Galois categories.

This is the form of the statement in which nothing beyond the exact functor `H`, the two Galois
categories and their chosen final objects is assumed: the continuous homomorphism of the
functoriality diagram is the one produced from the fibre-functor isomorphism `t`, and the
image of the chosen final object is seen to be final using exactness of `H`. -/
@[stacks 0BN6, sga "1 V 6.9" "more general", sga "1 V 6.10" "a) <=> fully faithful"]
public theorem surjective_inducedHom_tfae_of_fiberIso
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (hH : exactFunctor C C' H) (t : H ⋙ F' ≅ F)
    (star : C) (star' : C') (hstar : IsTerminal star) (hstar' : IsTerminal star') :
    List.TFAE
      [ Function.Surjective (galoisFunctorDataOfFiberIso F F' H t).hom,
        Nonempty H.FullyFaithful,
        ∀ X : C, PreGaloisCategory.IsConnected X →
          PreGaloisCategory.IsConnected (H.obj X),
        ∀ X : C, PreGaloisCategory.IsConnected X →
          Nonempty (star' ⟶ H.obj X) → Nonempty (star ⟶ X),
        ∀ X : C, Function.Bijective
          (mapFromTerminal H hstar' (isTerminalObjOfExactFunctor H hH hstar) X) ] :=
  surjective_inducedHom_tfae F F' H hH t (galoisFunctorDataOfFiberIso F F' H t)
    star star' hstar hstar' (isTerminalObjOfExactFunctor H hH hstar)

end CategoryTheory
