module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Pullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DirectImageAlgebraization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback commutes with completion

Let `f : X ⟶ Y` be a morphism of Noetherian schemes, let `𝒥 ⊆ 𝒪_Y` be a quasi-coherent sheaf of
ideals and set `ℐ = f^{-1}𝒥 𝒪_X`. Termwise pullback is a functor
`f^* : Coh(Y, 𝒥) ⟶ Coh(X, ℐ)` (Stacks 0887) and completion is a functor
`Coh(𝒪_Y) ⟶ Coh(Y, 𝒥)` (Stacks 0880). This file proves that the square commutes:

`(f^*𝒢) ^∧ ≅ f^*(𝒢 ^∧)` in `Coh(X, ℐ)`, naturally in the coherent `𝒪_Y`-module `𝒢`.

The comparison is the canonical one. The `n`-th term of `f^*(𝒢 ^∧)` is `f^*(𝒢 / 𝒥 ⁿ⁺¹ 𝒢)`, and
the pullbacks of the projections `𝒢 ⟶ 𝒢 / 𝒥 ⁿ⁺¹ 𝒢` form a cone on `f^*(𝒢 ^∧)` with vertex
`f^*𝒢`; by the mapping-out property of completion
(`Stacks.Algebraization.completionHomLimitEquiv`) that cone is a map of systems
`(f^*𝒢) ^∧ ⟶ f^*(𝒢 ^∧)`. It is an isomorphism termwise because pullback is right exact and
compatible with ideal-power multiples (`Stacks.Coherent.exists_functor_idealPowerQuotient_iso`).

## Main definitions

* `Stacks.Coherent.pullbackCoherentModules`: pullback as a functor `Coh(𝒪_Y) ⥤ Coh(𝒪_X)`,
  coherence of the pullback being Stacks 0EBF.
* `Stacks.Coherent.completionPullbackComparison`: the canonical map
  `(f^*𝒢) ^∧ ⟶ f^*(𝒢 ^∧)` in `Coh(X, ℐ)`.
* `Stacks.Coherent.completionPullbackIso`: the identification `(f^*𝒢) ^∧ ≅ f^*(𝒢 ^∧)`.
* `Stacks.Coherent.completionPullbackNatIso`: the identification as an isomorphism of functors
  `f^* ∘ (-)^∧ ≅ (-)^∧ ∘ f^*`.
* `Stacks.Coherent.pullbackCompletionDescent`: given an isomorphism `β : f^*(𝒢 ^∧) ≅ 𝓕 ^∧` and
  full faithfulness of completion on `X`, an isomorphism `f^*𝒢 ≅ 𝓕` of coherent `𝒪_X`-modules.

## Main results

* `Stacks.Coherent.completionProjection_completionPullbackComparison`: composed with the
  projection of `f^*𝒢` onto the `n`-th term of its completion, the comparison is the pullback of
  the projection of `𝒢` onto the `n`-th term of `𝒢 ^∧`.
* `Stacks.Coherent.isIso_completionPullbackComparison`: the comparison is an isomorphism.
* `Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_essImage`:
  Stacks 088B at a general base, assuming that `(𝒢_n)` is in the essential image of completion
  over `Y` and that completion on `X` is fully faithful.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Coherent

open Stacks.Algebraization

/-! ### Pullback of coherent modules -/

/-- **Pullback as a functor on coherent modules.** For a morphism `f : X ⟶ Y` of schemes with `X`
locally Noetherian, termwise pullback of sheaves of modules preserves coherence (Stacks 0EBF), so
it restricts to a functor `Coh(𝒪_Y) ⥤ Coh(𝒪_X)`. -/
public def pullbackCoherentModules {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y) :
    AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf ⥤
      AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf where
  obj 𝒢 :=
    ⟨(Scheme.Modules.pullback f).obj 𝒢.obj,
      haveI : 𝒢.obj.IsCoherent := 𝒢.property
      AlgebraicGeometry.isCoherent_pullback f 𝒢.obj⟩
  map u := ObjectProperty.homMk ((Scheme.Modules.pullback f).map u.hom)
  map_id 𝒢 := ObjectProperty.hom_ext _ ((Scheme.Modules.pullback f).map_id 𝒢.obj)
  map_comp u v := ObjectProperty.hom_ext _ ((Scheme.Modules.pullback f).map_comp u.hom v.hom)

/-- The underlying module of the pullback of a coherent module is the pullback of its underlying
module. -/
public theorem pullbackCoherentModules_obj_obj {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Y) (𝒢 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) :
    ((pullbackCoherentModules f).obj 𝒢).obj = (Scheme.Modules.pullback f).obj 𝒢.obj :=
  rfl

/-- The underlying morphism of the pullback of a morphism of coherent modules is the pullback of
its underlying morphism. -/
public theorem pullbackCoherentModules_map_hom {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Y) {𝒢 𝒢' : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf}
    (u : 𝒢 ⟶ 𝒢') :
    ((pullbackCoherentModules f).map u).hom = (Scheme.Modules.pullback f).map u.hom :=
  rfl

/-! ### The comparison map `(f^*𝒢) ^∧ ⟶ f^*(𝒢 ^∧)` -/

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
  (J : Y.IdealSheafData) (𝒢 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)

/-- The map from `f^*𝒢` into the inverse limit of `f^*(𝒢 ^∧)`, namely the pullback of the cone of
projections of `𝒢` onto the terms of `𝒢 ^∧`. -/
public def pullbackCompletionLift :
    coherentObj ((pullbackCoherentModules f).obj 𝒢) ⟶
      limit (C := X.Modules)
        ((coherentAdicPullback f J).obj ((completionFunctor Y J).obj 𝒢)).obj :=
  limit.lift _ ((Scheme.Modules.pullback f).mapCone (Stacks.Algebraization.completionCone Y J 𝒢))

/-- Its composite with the `n`-th limit projection is the pullback of the `n`-th projection of
`𝒢`. -/
public theorem pullbackCompletionLift_π (n : ℕᵒᵖ) :
    pullbackCompletionLift f J 𝒢 ≫
        limit.π ((coherentAdicPullback f J).obj ((completionFunctor Y J).obj 𝒢)).obj n =
      (Scheme.Modules.pullback f).map (completionProjection Y J 𝒢 n.unop) :=
  limit.lift_π ((Scheme.Modules.pullback f).mapCone (Stacks.Algebraization.completionCone Y J 𝒢)) n

/-- **The canonical comparison `(f^*𝒢) ^∧ ⟶ f^*(𝒢 ^∧)`**, as a morphism of coherent adic systems
along `ℐ = f^{-1}𝒥 𝒪_X`.

It is the map of systems out of a completion determined, by
`Stacks.Algebraization.completionHomLimitEquiv`, by the morphism
`f^*𝒢 ⟶ lim f^*(𝒢 / 𝒥 ⁿ⁺¹ 𝒢)` assembled from the pullbacks of the projections of `𝒢`. -/
public def completionPullbackComparison :
    (completionFunctor X (J.comap f)).obj ((pullbackCoherentModules f).obj 𝒢) ⟶
      (coherentAdicPullback f J).obj ((completionFunctor Y J).obj 𝒢) :=
  homToAdicSystem ((pullbackCoherentModules f).obj 𝒢)
    ((coherentAdicPullback f J).obj ((completionFunctor Y J).obj 𝒢))
    (pullbackCompletionLift f J 𝒢)

/-- **The normalization of the comparison.** Composing the `n`-th component of
`(f^*𝒢) ^∧ ⟶ f^*(𝒢 ^∧)` with the projection of `f^*𝒢` onto the `n`-th term of its completion
gives the pullback of the projection of `𝒢` onto the `n`-th term of `𝒢 ^∧`. -/
public theorem completionProjection_completionPullbackComparison (n : ℕᵒᵖ) :
    completionProjection X (J.comap f) ((pullbackCoherentModules f).obj 𝒢) n.unop ≫
        (completionPullbackComparison f J 𝒢).hom.app n =
      (Scheme.Modules.pullback f).map (completionProjection Y J 𝒢 n.unop) :=
  (completionProjection_homToAdicSystem _ _ (pullbackCompletionLift f J 𝒢) n).trans
    (pullbackCompletionLift_π f J 𝒢 n)

/-- The `n`-th term of the comparison is an isomorphism. -/
public theorem isIso_completionPullbackComparison_app (n : ℕᵒᵖ) :
    IsIso ((completionPullbackComparison f J 𝒢).hom.app n) := by
  set L := Scheme.Modules.pullback f with hL
  set m := n.unop with hm
  set P := (pullbackCoherentModules f).obj 𝒢 with hP
  obtain ⟨e, he⟩ := exists_functor_idealPowerQuotient_iso L J (J.comap f) (m + 1) 𝒢.obj
    (fun {N} φ => pullback_idealPowerMultiple_comp_eq_zero_iff f J (m + 1) 𝒢.obj φ)
  let wIso : ((coherentAdicPullback f J).obj ((completionFunctor Y J).obj 𝒢)).obj.obj n ≅
      ((completionFunctor X (J.comap f)).obj P).obj.obj n :=
    L.mapIso (eqToIso (completionFunctor_obj Y J 𝒢 m)) ≪≫ e ≪≫
      eqToIso (completionFunctor_obj X (J.comap f) P m).symm
  have hwdef : wIso.hom = L.map (eqToHom (completionFunctor_obj Y J 𝒢 m)) ≫ e.hom ≫
      eqToHom (completionFunctor_obj X (J.comap f) P m).symm := rfl
  have hinner : completionProjection Y J 𝒢 m ≫ eqToHom (completionFunctor_obj Y J 𝒢 m) =
      cokernel.π (idealPowerMultiple J (m + 1) 𝒢.obj).ι :=
    (Category.assoc (cokernel.π (idealPowerMultiple J (m + 1) 𝒢.obj).ι)
        (eqToHom (completionFunctor_obj Y J 𝒢 m).symm)
        (eqToHom (completionFunctor_obj Y J 𝒢 m))).trans
      ((congrArg (fun k => cokernel.π (idealPowerMultiple J (m + 1) 𝒢.obj).ι ≫ k)
          ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans (Category.comp_id _))
  have hkey : L.map (completionProjection Y J 𝒢 m) ≫ wIso.hom =
      completionProjection X (J.comap f) P m := by
    have h1 : L.map (completionProjection Y J 𝒢 m) ≫
        L.map (eqToHom (completionFunctor_obj Y J 𝒢 m)) =
          L.map (cokernel.π (idealPowerMultiple J (m + 1) 𝒢.obj).ι) :=
      (L.map_comp _ _).symm.trans (congrArg L.map hinner)
    refine (congrArg (fun k => L.map (completionProjection Y J 𝒢 m) ≫ k) hwdef).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ (e.hom ≫
      eqToHom (completionFunctor_obj X (J.comap f) P m).symm)) h1).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (fun k => k ≫ eqToHom (completionFunctor_obj X (J.comap f) P m).symm) he
  have hepi := Stacks.Algebraization.epi_completionProjection X (J.comap f) P m
  have hfac : (completionPullbackComparison f J 𝒢).hom.app n ≫ wIso.hom = 𝟙 _ :=
    (@cancel_epi _ _ _ _ _ (completionProjection X (J.comap f) P m) hepi _ _).mp
      ((Category.assoc _ _ _).symm.trans
        (((congrArg (fun k => k ≫ wIso.hom)
            (completionProjection_completionPullbackComparison f J 𝒢 n)).trans
          hkey).trans (Category.comp_id _).symm))
  exact IsIso.of_isIso_fac_right hfac

/-- **The comparison `(f^*𝒢) ^∧ ⟶ f^*(𝒢 ^∧)` is an isomorphism.** -/
public theorem isIso_completionPullbackComparison :
    IsIso (completionPullbackComparison f J 𝒢) := by
  have : ∀ n : ℕᵒᵖ, IsIso ((completionPullbackComparison f J 𝒢).hom.app n) :=
    isIso_completionPullbackComparison_app f J 𝒢
  have : IsIso (completionPullbackComparison f J 𝒢).hom :=
    NatIso.isIso_of_isIso_app _
  exact (ObjectProperty.isIso_hom_iff _).mp inferInstance

/-- **Pullback commutes with completion: `(f^*𝒢) ^∧ ≅ f^*(𝒢 ^∧)`.** For a morphism `f : X ⟶ Y` of
Noetherian schemes, a quasi-coherent sheaf of ideals `𝒥` on `Y` and a coherent `𝒪_Y`-module `𝒢`,
the completion along `ℐ = f^{-1}𝒥 𝒪_X` of the pullback of `𝒢` is the termwise pullback of the
completion of `𝒢` along `𝒥`. -/
@[ega "I 10.9.5" "special case"]
public def completionPullbackIso :
    (completionFunctor X (J.comap f)).obj ((pullbackCoherentModules f).obj 𝒢) ≅
      (coherentAdicPullback f J).obj ((completionFunctor Y J).obj 𝒢) :=
  haveI := isIso_completionPullbackComparison f J 𝒢
  asIso (completionPullbackComparison f J 𝒢)

/-- The isomorphism `(f^*𝒢) ^∧ ≅ f^*(𝒢 ^∧)` is the canonical comparison. -/
public theorem completionPullbackIso_hom :
    (completionPullbackIso f J 𝒢).hom = completionPullbackComparison f J 𝒢 :=
  rfl

/-- **Pullback commutes with completion, naturally: `(-)^∧ ∘ f^* ≅ f^* ∘ (-)^∧`.** The
isomorphisms `(f^*𝒢) ^∧ ≅ f^*(𝒢 ^∧)` of `Stacks.Coherent.completionPullbackIso` are the
components of an isomorphism of functors `Coh(𝒪_Y) ⥤ Coh(X, ℐ)`. -/
public def completionPullbackNatIso :
    pullbackCoherentModules f ⋙ completionFunctor X (J.comap f) ≅
      completionFunctor Y J ⋙ coherentAdicPullback f J :=
  NatIso.ofComponents (fun 𝒢 => completionPullbackIso f J 𝒢) (by
    intro 𝒢 𝒢' u
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
    have hepi := Stacks.Algebraization.epi_completionProjection X (J.comap f)
      ((pullbackCoherentModules f).obj 𝒢) n.unop
    refine (@cancel_epi _ _ _ _ _ (completionProjection X (J.comap f)
      ((pullbackCoherentModules f).obj 𝒢) n.unop) hepi _ _).mp ?_
    change completionProjection X (J.comap f) ((pullbackCoherentModules f).obj 𝒢) n.unop ≫
        (((completionFunctor X (J.comap f)).map ((pullbackCoherentModules f).map u)).hom.app n ≫
          (completionPullbackComparison f J 𝒢').hom.app n) =
      completionProjection X (J.comap f) ((pullbackCoherentModules f).obj 𝒢) n.unop ≫
        ((completionPullbackComparison f J 𝒢).hom.app n ≫
          ((coherentAdicPullback f J).map ((completionFunctor Y J).map u)).hom.app n)
    have hleft : completionProjection X (J.comap f) ((pullbackCoherentModules f).obj 𝒢) n.unop ≫
        (((completionFunctor X (J.comap f)).map ((pullbackCoherentModules f).map u)).hom.app n ≫
          (completionPullbackComparison f J 𝒢').hom.app n) =
        (Scheme.Modules.pullback f).map
          (u.hom ≫ completionProjection Y J 𝒢' n.unop) := by
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun k => k ≫ (completionPullbackComparison f J 𝒢').hom.app n)
        (completionFunctor_map_quotient X (J.comap f)
          ((pullbackCoherentModules f).map u) n.unop)).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun k => (Scheme.Modules.pullback f).map u.hom ≫ k)
        (completionProjection_completionPullbackComparison f J 𝒢' n)).trans ?_
      exact ((Scheme.Modules.pullback f).map_comp u.hom
        (completionProjection Y J 𝒢' n.unop)).symm
    have hright : completionProjection X (J.comap f) ((pullbackCoherentModules f).obj 𝒢) n.unop ≫
        ((completionPullbackComparison f J 𝒢).hom.app n ≫
          ((coherentAdicPullback f J).map ((completionFunctor Y J).map u)).hom.app n) =
        (Scheme.Modules.pullback f).map
          (u.hom ≫ completionProjection Y J 𝒢' n.unop) := by
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun k => k ≫
        ((coherentAdicPullback f J).map ((completionFunctor Y J).map u)).hom.app n)
        (completionProjection_completionPullbackComparison f J 𝒢 n)).trans ?_
      refine ((Scheme.Modules.pullback f).map_comp (completionProjection Y J 𝒢 n.unop)
        (((completionFunctor Y J).map u).hom.app n)).symm.trans ?_
      exact congrArg (Scheme.Modules.pullback f).map
        (completionFunctor_map_quotient Y J u n.unop)
    exact hleft.trans hright.symm)

/-- The components of the natural isomorphism are the comparison maps. -/
public theorem completionPullbackNatIso_hom_app :
    (completionPullbackNatIso f J).hom.app 𝒢 = completionPullbackComparison f J 𝒢 :=
  rfl

/-! ### Descending the isomorphism `β` of Stacks 088B -/

/-- **The descent of `β`.** Let `f : X ⟶ Y` be a morphism of Noetherian schemes, let `𝒢` be a
coherent `𝒪_Y`-module and `𝓕` a coherent `𝒪_X`-module, and suppose completion along
`ℐ = f^{-1}𝒥 𝒪_X` is fully faithful on `Coh(𝒪_X)`. Then an isomorphism

`β : f^*(𝒢 ^∧) ≅ 𝓕 ^∧`

of coherent adic systems on `X` descends to an isomorphism `f^*𝒢 ≅ 𝓕` of coherent
`𝒪_X`-modules. -/
public def pullbackCompletionDescent
    (hff : Nonempty (completionFunctor X (J.comap f)).FullyFaithful)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (β : (coherentAdicPullback f J).obj ((completionFunctor Y J).obj 𝒢) ≅
      (completionFunctor X (J.comap f)).obj 𝓕) :
    (Scheme.Modules.pullback f).obj 𝒢.obj ≅ 𝓕.obj :=
  let ei := hff.some.preimageIso (completionPullbackIso f J 𝒢 ≪≫ β)
  ⟨ei.hom.hom, ei.inv.hom, ObjectProperty.isoHom_inv_id_hom ei,
    ObjectProperty.isoInv_hom_id_hom ei⟩

/-! ### Stacks 088B at a general base -/

/-- **Stacks 088B at a general base.** Let `f : X ⟶ Y` be a proper
morphism of Noetherian schemes, let `𝒥, 𝒦 ⊆ 𝒪_Y` be quasi-coherent sheaves of ideals, let
`(𝒢_n)` be an object of `Coh(Y, 𝒥)` and let `𝓕` be a coherent `𝒪_X`-module. Suppose given

* `halg`: `(𝒢_n)` is in the essential image of completion over `Y`;
* `hff`: completion along `ℐ` is fully faithful on `Coh(𝒪_X)`;
* `β : f^*(𝒢_n) ≅ 𝓕 ^∧`, an isomorphism in `Coh(X, ℐ)`;
* `hc`: for every algebraization `𝒢` of `(𝒢_n)` the adjunction map `𝒢 ⟶ f_*f^*𝒢` restricts to
  an isomorphism on `V = Y ∖ V(𝒦)`.

Then there is a morphism

`α : (𝒢_n) ⟶ (f_*𝓕) ^∧`

of inverse systems of `𝒪_Y`-modules whose levelwise kernels and cokernels are annihilated by a
power of `𝒦`. -/
public theorem exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_essImage
    [IsProper f] (K : Y.IdealSheafData)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (G : CoherentAdicSystems J)
    (halg : (completionFunctor Y J).essImage G)
    (hff : Nonempty (completionFunctor X (J.comap f)).FullyFaithful)
    (β : (coherentAdicPullback f J).obj G ≅ (completionFunctor X (J.comap f)).obj 𝓕)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf,
      (G ≅ (completionFunctor Y J).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι K.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app 𝒜.obj))) :
    ∃ α : G.obj ⟶ ((completionFunctor Y J).obj (properPushforwardCoherent f 𝓕)).obj,
      IsKernelCokernelAnnihilatedByPower K α := by
  obtain ⟨𝒜, ⟨ealg⟩⟩ := halg
  let e : G ≅ (completionFunctor Y J).obj 𝒜 := ealg.symm
  let b : (Scheme.Modules.pullback f).obj 𝒜.obj ≅ 𝓕.obj :=
    pullbackCompletionDescent f J 𝒜 hff 𝓕
      (((coherentAdicPullback f J).mapIso e).symm ≪≫ β)
  exact exists_isKernelCokernelAnnihilatedByPower_properDirectImage f J K 𝒜 𝓕 b G
    ((ObjectProperty.ι (IsCoherentAdicSystem J)).mapIso e) (hc 𝒜 e)

end Stacks.Coherent

end
