module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Pushforward
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.RestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
import StacksCore.Tactic.StacksAttribute

/-!
# Localization and derived completeness

Let `(𝒞, 𝒪)` be a ringed site, let `ℐ ⊂ 𝒪` be a sheaf of ideals and let `U` be an object of
`𝒞`. [Stacks, Tag 0A0F] asserts that derived completion commutes with restriction to the
localized ringed site `(𝒞/U, 𝒪_U)`. This file proves the half of that statement which does not
mention the completion functor: restriction to `𝒞/U` carries a complex derived complete along
`ℐ` to one derived complete along the restriction of `ℐ`.

## Main definitions

* `AlgebraicGeometry.RingedSite.overIdeal`: the restriction `ℐ|_U` of a sheaf of ideals to a
  slice site, whose sections over `V` are the sections of `ℐ` over `V.left`.

## Main results

* `AlgebraicGeometry.RingedSite.restrict_isDerivedComplete_overIdeal`: **restriction preserves
  derived completeness**, the first step of [Stacks, Tag 0A0F].
* `AlgebraicGeometry.RingedSite.restrict_isDerivedComplete`: the same with the restricted sheaf
  of ideals left a parameter, required only to have its local sections among those of `ℐ`,
  which is all the proof uses.

## Implementation notes

*Why the iterated slice appears.* `AlgebraicGeometry.RingedSite.IsDerivedComplete` of
[Stacks, Tag 0999] tests a complex `K` on `(𝒞, 𝒪)` object by object: for every `V` and every
`g ∈ ℐ(V)` it asks that the Milnor difference `1 - g·shift` be invertible on the countable
product of copies of `K|_V` in `D(𝒪_V)`. Applied to the *localized* ringed site
`AlgebraicGeometry.RingedSite.over`, whose underlying category is `𝒞/U`, the test runs over the
objects `W` of `𝒞/U` and takes place on `(𝒞/U)/W`, the **iterated** slice — whereas the
hypothesis, being about `(𝒞, 𝒪)`, speaks of the slice `𝒞/W.left`. The proof is therefore the
transport of the Milnor condition from `D(𝒪_{W.left})` to `D(𝒪_{(𝒞/U)/W})`.

*The functor along which it is transported.* `𝒞/W.left ≌ (𝒞/U)/W` is
`CategoryTheory.Over.iteratedSliceEquiv`, and the induced equivalence of categories of sheaves
of modules is `Stacks.SheafOfModules.InternalHom.sliceModulesEquiv`. The transport needs that
equivalence's *functor*, from the slice to the iterated slice: the companion functor
`Stacks.SheafOfModules.sliceBackward` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/IteratedSlice.lean` goes the other way, and so
rewrites a hypothesis stated on the iterated slice rather than producing a conclusion there.
`sliceModulesEquiv_functor` records that this functor is a `SheafOfModules.pushforward`, which
is what makes the two lemmas below applicable to it; the statement is an `rfl`.

*Why restriction twice is restriction once.* `overFunctor_comp_sliceModulesEquiv_functor` is
again an **equality** of functors, by `rfl`, and for the same reason as
`Stacks.SheafOfModules.overFunctor_comp_sliceBackward`: `SheafOfModules.pushforwardComp` is an
`Iso.refl`, so a composite of pushforwards *is* the pushforward of the composite of the site
functors, and `CategoryTheory.Over.iteratedSliceForward_forget` identifies the relevant two
composites of site functors, once more by `rfl`.

*The three inputs to the transport.* `isDerivedCompleteAt_map_of_smul_id` of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/RestrictScalars.lean`
asks for an additive functor which preserves countable products and which matches the two
scalars. Here:

* additivity is additivity of a pushforward of sheaves of modules;
* the countable products are preserved because the functor on derived categories is a *right*
  adjoint: `sliceModulesEquiv` is an equivalence, so its inverse is left adjoint to its functor,
  and an adjunction of exact functors derives to an adjunction of derived categories
  (`CategoryTheory.Adjunction.mapDerivedCategory`). This is the same device as
  `AlgebraicGeometry.RingedSite.DerivedRestrictScalars.preservesProducts_mapDerivedCategory`
  uses for restriction of scalars, and it avoids the exactness of countable products
  (Grothendieck's AB4*), which fails for sheaves of modules;
* the scalars match already at the level of sheaves of modules, by
  `Stacks.SheafOfModules.map_globalSectionToEnd`, because the two compatible families of local
  sections attached to `g` — over `𝒞/W.left` and over `(𝒞/U)/W` — restrict `g` along the same
  arrow of `𝒞`, which is `Stacks.SheafOfModules.terminalSection_over_val` read on both sides.
  It is lifted to the derived category by
  `AlgebraicGeometry.RingedSite.mapDerivedCategory_map_smul_id`.

### The rest of Tag 0A0F

Tag 0A0F asserts more: that the completion functor itself commutes with restriction, i.e. that
the left adjoint `D(𝒪) ⥤ D_comp(𝒪, ℐ)` of [Stacks, Tag 099F] and its localized counterpart are
intertwined by restriction, compatibly with the two units. That comparison is in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LocalizationCompletion`:
`AlgebraicGeometry.RingedSite.derivedCompletionRestrictComparison`, the Remark's map
`a : (K|_U)^∧ ⟶ K^∧|_U`, whose construction is this theorem plus the universal property of the
completion of `K|_U`. That `a` is an isomorphism at every `K`, and so that `K^∧|_U` *is* the
derived completion of `K|_U`, is
`AlgebraicGeometry.RingedSite.isIso_derivedCompletionRestrictComparison_overIdeal_app` and
`AlgebraicGeometry.RingedSite.derivedCompletion_restrict` of
`LocalizationCompletionFiniteType.lean`, for `ℐ` of finite type and the completion functors of
[Stacks, Tag 099F] on both sites; the latter carries the tag.

The comparison map is stated in `LocalizationCompletion.lean` for an arbitrary sheaf of ideals,
taking the conclusion of [Stacks, Tag 099F] on each of the two sites as a typeclass input; for a
sheaf of ideals of finite type both inputs are the instance of [Stacks, Tag 099F] itself,
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete`, and that is the generality of
`AlgebraicGeometry.RingedSite.derivedCompletion_restrict` of
`LocalizationCompletionFiniteType.lean`.

The Remark's second map `b : K^∧ ⟶ Rj_*((K|_U)^∧)` belongs to its alternative argument; it is
`AlgebraicGeometry.RingedSite.derivedCompletion_restrict_secondMap` of
`LocalizationCompletionPushforward.lean`.

`restrict_isDerivedComplete` is stated with the restricted sheaf of ideals as a parameter,
required only to have its local sections among those of `ℐ`, which is all the proof uses.
`overIdeal` constructs `ℐ|_U` with sections *equal*, by definition, to those of `ℐ`, and
`restrict_isDerivedComplete_overIdeal` is the resulting statement about that object. Locality
of membership for `ℐ|_U` is locality for `ℐ`: the pushforward along `CategoryTheory.Over.forget`
of the sieve of a section of `ℐ|_U` is contained in the sieve of that same section read on `𝒞`,
by `CategoryTheory.Sieve.overEquiv_iff`, and a sieve containing a covering sieve covers.

## References

* [Stacks Project, Tag 0A0F](https://stacks.math.columbia.edu/tag/0A0F)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

universe u v w

namespace AlgebraicGeometry.RingedSite

/-- The functor of the iterated-slice equivalence of sheaves of modules is a pushforward of
sheaves of modules, namely the one along `CategoryTheory.Over.iteratedSliceForward`. -/
theorem sliceModulesEquiv_functor (X : RingedSite.{u, v, max u v}) (U : X.C) (W : Over U) :
    (Stacks.SheafOfModules.InternalHom.sliceModulesEquiv.{u, v, max u v, max u v}
        X U W).functor =
      SheafOfModules.pushforward.{max u v}
        (F := (Over.iteratedSliceEquiv W).functor) (𝟙 _) := rfl

/-- **Restricting to the slice at `W.left` and transporting to the iterated slice is
restricting twice.** An equality of functors, by `rfl`; see the implementation notes. -/
theorem overFunctor_comp_sliceModulesEquiv_functor
    (X : RingedSite.{u, v, max u v}) (U : X.C) (W : Over U) :
    SheafOfModules.overFunctor.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) W.left ⋙
        (Stacks.SheafOfModules.InternalHom.sliceModulesEquiv.{u, v, max u v, max u v}
          X U W).functor =
      SheafOfModules.overFunctor.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U ⋙
        SheafOfModules.overFunctor.{max u v}
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U) W := rfl

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, v, max u v})

/-- The structure sheaf of a ringed site, with commutativity forgotten, still has commutative
multiplication on sections. The site-object, morphism, and coefficient universes are independent;
the instance supplies the sectionwise hypothesis of `isMulCommutative_sheafOver`. -/
instance isMulCommutative_ringSheaf_obj' (X : RingedSite.{u, v, w}) (V : X.Cᵒᵖ) :
    IsMulCommutative (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj V) :=
  inferInstanceAs (IsMulCommutative (X.O.obj.obj V))

/-- **A restriction of a sheaf of commutative rings to a slice site is a sheaf of commutative
rings.** Stated so that instance search finds it at every depth of iterated slice, each level
peeling off one `CategoryTheory.Over.forget`. -/
instance isMulCommutative_sheafOver {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
    [∀ V : Cᵒᵖ, IsMulCommutative (R.obj.obj V)] (U : C) (V : (Over U)ᵒᵖ) :
    IsMulCommutative ((R.over U).obj.obj V) :=
  inferInstanceAs (IsMulCommutative (R.obj.obj (op (unop V).left)))

/-- **The restriction of a sheaf of ideals to a slice site.** Its sections over an object `V`
of `C/U` are the sections of `ℐ` over `V.left`; membership is local for the slice topology
exactly because it is local for `J`, the sieve of an object's section pushing forward to a
sieve contained in the sieve of that same section read on `C`. -/
def overIdeal {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (I : SheafOfModules.Submodule (SheafOfModules.unit R)) (U : C) :
    SheafOfModules.Submodule (SheafOfModules.unit (R.over U)) where
  obj V := I.toSubmodule.obj (op (unop V).left)
  map f := I.toSubmodule.map (Quiver.Hom.op (Over.Hom.left f.unop))
  isSheaf {V} s hs := by
    refine I.isSheaf s (J.superset_covering ?_ ((J.mem_over_iff _).mp hs))
    intro Z f hf
    exact (Sieve.overEquiv_iff _ f).mp hf

/-- The sections of a restricted sheaf of ideals, by definition. -/
theorem overIdeal_toSubmodule_obj {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (I : SheafOfModules.Submodule (SheafOfModules.unit R)) (U : C)
    (V : (Over U)ᵒᵖ) :
    (overIdeal I U).toSubmodule.obj V = I.toSubmodule.obj (op (unop V).left) := rfl

/-- Continuity of the functor of the iterated-slice equivalence for the slice topologies, in
the spelling instance search needs: Mathlib states it for
`CategoryTheory.Over.iteratedSliceForward`. -/
@[sga "3 IV 4.5.1" "partial"]
instance isContinuous_iteratedSliceEquiv_functor {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {U : C} (W : Over U) :
    (Over.iteratedSliceEquiv W).functor.IsContinuous ((J.over U).over W) (J.over W.left) :=
  inferInstanceAs (W.iteratedSliceForward.IsContinuous ((J.over U).over W) (J.over W.left))

/-- **The iterated-slice transport matches the two multiplication operators attached to a
section.** The compatible family of local sections of `R` which a section `g` over `W.left`
defines on `C/W.left`, and the one it defines on the iterated slice `(C/U)/W`, both restrict
`g` along the arrow of `C` underlying an object of the iterated slice; so the pushforward of
sheaves of modules along `CategoryTheory.Over.iteratedSliceForward` carries multiplication by
the first to multiplication by the second. -/
theorem pushforward_iteratedSlice_map_terminalSectionToEnd {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
    [∀ V : Cᵒᵖ, IsMulCommutative (R.obj.obj V)] (U : C) (W : Over U)
    (g : R.obj.obj (op W.left)) (M : SheafOfModules.{w} (R.over W.left)) :
    (SheafOfModules.pushforward.{w} (F := (Over.iteratedSliceEquiv W).functor)
          (𝟙 ((R.over U).over W))).map
        ((Stacks.SheafOfModules.terminalSectionToEnd (R.over W.left) (Over.mk (𝟙 W.left))
            Over.mkIdTerminal g).app M) =
      (Stacks.SheafOfModules.terminalSectionToEnd ((R.over U).over W) (Over.mk (𝟙 W))
            Over.mkIdTerminal g).app
        ((SheafOfModules.pushforward.{w} (F := (Over.iteratedSliceEquiv W).functor)
            (𝟙 ((R.over U).over W))).obj M) :=
  Stacks.SheafOfModules.map_globalSectionToEnd
    (F := (Over.iteratedSliceEquiv W).functor)
    (S := (R.over U).over W) (R := R.over W.left) (𝟙 ((R.over U).over W))
    (Stacks.SheafOfModules.terminalSection (R.over W.left) (Over.mk (𝟙 W.left))
      Over.mkIdTerminal g)
    (Stacks.SheafOfModules.terminalSection ((R.over U).over W) (Over.mk (𝟙 W))
      Over.mkIdTerminal g)
    (fun T => (Stacks.SheafOfModules.terminalSection_over_val (R.over U) W g T).trans
      (Stacks.SheafOfModules.terminalSection_over_val R W.left g
        (op ((Over.iteratedSliceEquiv W).functor.obj (unop T)))).symm) M

/-- `pushforward_iteratedSlice_map_terminalSectionToEnd` read through the iterated-slice
equivalence of sheaves of modules, whose functor is that pushforward by
`sliceModulesEquiv_functor`. -/
theorem sliceModulesEquiv_functor_map_terminalSectionToEnd
    (X : RingedSite.{u, v, max u v}) (U : X.C) (W : Over U)
    (g : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op W.left))
    (M : SheafOfModules.{max u v} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over W.left)) :
    (Stacks.SheafOfModules.InternalHom.sliceModulesEquiv.{u, v, max u v, max u v}
          X U W).functor.map
        ((Stacks.SheafOfModules.terminalSectionToEnd
            (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over W.left)
            (Over.mk (𝟙 W.left)) Over.mkIdTerminal g).app M) =
      (Stacks.SheafOfModules.terminalSectionToEnd
            ((((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).over W)
            (Over.mk (𝟙 W)) Over.mkIdTerminal g).app
        ((Stacks.SheafOfModules.InternalHom.sliceModulesEquiv.{u, v, max u v, max u v}
            X U W).functor.obj M) :=
  pushforward_iteratedSlice_map_terminalSectionToEnd ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    U W g M

/-- **Restriction to a localized ringed site preserves derived completeness**, the first step of
[Stacks, Tag 0A0F]. Let `ℐ ⊂ 𝒪` be a sheaf of ideals on a ringed site `(𝒞, 𝒪)`, let `U` be an
object of `𝒞` and let `ℐ_U` be a sheaf of ideals on the localized ringed site `(𝒞/U, 𝒪_U)`
whose local sections are local sections of `ℐ`. If `K` is derived complete along `ℐ`, then its
restriction `K|_U` is derived complete along `ℐ_U`.

The Milnor condition of [Stacks, Tag 0999] for `K|_U` at a section `g ∈ ℐ_U(W)` lives on the
iterated slice `(𝒞/U)/W`, while the hypothesis provides it on the slice `𝒞/W.left`. The two
are identified by `CategoryTheory.Over.iteratedSliceEquiv`; the induced equivalence of
categories of sheaves of modules is a pushforward, which is additive, carries multiplication by
`g` read on `𝒞/W.left` to multiplication by `g` read on `(𝒞/U)/W`, and — being one half of an
equivalence, hence a right adjoint — commutes with the countable products of the derived
categories. -/
theorem restrict_isDerivedComplete
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) (U : X.C)
    (IU : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))))
    (hIU : ∀ (W : Over U)
        (g : ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).obj.obj (op W)),
      g ∈ IU.toSubmodule.obj (op W) → g ∈ I.toSubmodule.obj (op W.left))
    (K : DerivedCategory (SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hK : IsDerivedComplete.{u, v, max u v, max u v} X I K) :
    let F := SheafOfModules.overFunctor.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U
    ∃ hAdd : F.Additive,
    ∃ hLim : PreservesFiniteLimits F,
    ∃ hColim : PreservesFiniteColimits F,
      letI : F.Additive := hAdd
      letI : PreservesFiniteLimits F := hLim
      letI : PreservesFiniteColimits F := hColim
      IsDerivedComplete.{max u v, v, max u v, max u v} (X.over U) IU
        (F.mapDerivedCategory.obj K) := by
  have hLimU : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U
  have hColimU : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U
  refine ⟨inferInstance, hLimU, hColimU, ?_⟩
  let := hLimU
  let := hColimU
  intro W g hg
  -- the slice data of Tag 0999 for the localized site at `W`, which is the iterated slice
  let RW := ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).over W
  let AW := SheafOfModules.{max u v} RW
  let : Linear (CatCenter AW) AW := Linear.ofRingMorphism (RingHom.id (CatCenter AW))
  -- the second spelling of the iterated slice: the restriction of the restriction of `𝒪`
  let RW' := (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).over W
  let AW' := SheafOfModules.{max u v} RW'
  let : Linear (CatCenter AW) AW' := Linear.ofRingMorphism (RingHom.id (CatCenter AW))
  have hLimW : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{max u v}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) W) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits W
  have hColimW : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{max u v}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) W) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits W
  have hLimW' : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{max u v}
        (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U) W) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits W
  have hColimW' : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{max u v}
        (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U) W) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits W
  let := hLimW'
  let := hColimW'
  have hProdW : HasProductsOfShape ℕ (DerivedCategory AW) :=
    hasProductsOfShape_nat_derivedCategory_over.{max u v, v, max u v} (X.over U) W
  refine ⟨inferInstance, hLimW, hColimW, hProdW, ?_⟩
  let := hProdW
  have hProdW' : HasProductsOfShape ℕ (DerivedCategory AW') := hProdW
  let := hProdW'
  -- the same data on the slice at `W.left`, where the hypothesis lives
  let RL := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over W.left
  let AL := SheafOfModules.{max u v} RL
  let : Linear (CatCenter AL) AL := Linear.ofRingMorphism (RingHom.id (CatCenter AL))
  have hProdL : HasProductsOfShape ℕ (DerivedCategory AL) :=
    hasProductsOfShape_nat_derivedCategory_over.{u, v, max u v} X W.left
  let := hProdL
  obtain ⟨hAddL, hLimL, hColimL, hProdL', hKW⟩ := hK W.left g (hIU W g hg)
  let := hAddL
  let := hLimL
  let := hColimL
  -- the transport functor: the iterated-slice equivalence of sheaves of modules
  let E := Stacks.SheafOfModules.InternalHom.sliceModulesEquiv.{u, v, max u v, max u v} X U W
  let Φ := E.functor
  have hΦadd : Φ.Additive :=
    inferInstanceAs (SheafOfModules.pushforward.{max u v}
      (F := (Over.iteratedSliceEquiv W).functor) (𝟙 _)).Additive
  let := hΦadd
  have hΨadd : E.inverse.Additive :=
    inferInstanceAs (SheafOfModules.pushforward.{max u v}
      (F := (Over.iteratedSliceEquiv W).inverse) (𝟙 _)).Additive
  let := hΨadd
  have hΦeq : Φ.IsEquivalence := inferInstanceAs E.functor.IsEquivalence
  let := hΦeq
  have hΨeq : E.inverse.IsEquivalence := inferInstanceAs E.inverse.IsEquivalence
  let := hΨeq
  have hΦlim : PreservesFiniteLimits Φ := inferInstance
  let := hΦlim
  have hΦcolim : PreservesFiniteColimits Φ := inferInstance
  let := hΦcolim
  have hΨlim : PreservesFiniteLimits E.inverse := inferInstance
  let := hΨlim
  have hΨcolim : PreservesFiniteColimits E.inverse := inferInstance
  let := hΨcolim
  -- countable products: `Φ` on derived categories is a right adjoint
  have hpl : PreservesLimitsOfShape (Discrete ℕ) Φ.mapDerivedCategory := by
    have adjD : E.inverse.mapDerivedCategory ⊣ Φ.mapDerivedCategory :=
      CategoryTheory.Adjunction.mapDerivedCategory E.symm.toAdjunction
    have := adjD.rightAdjoint_preservesLimits
    infer_instance
  let := hpl
  -- the two scalars, and the fact that `Φ` matches them
  let aL : CatCenter AL :=
    Stacks.SheafOfModules.terminalSectionToEnd RL (Over.mk (𝟙 W.left)) Over.mkIdTerminal g
  let aW : CatCenter AW :=
    Stacks.SheafOfModules.terminalSectionToEnd RW (Over.mk (𝟙 W)) Over.mkIdTerminal g
  -- the scalars agree already on sheaves of modules: both restrict `g` along the same arrow
  have hmap : ∀ M : AL, Φ.map (aL.app M) = aW.app (Φ.obj M) :=
    sliceModulesEquiv_functor_map_terminalSectionToEnd X U W g
  -- `aL • 𝟙 M` of the `Linear` structure of Tag 0999 is `aL.app M ≫ 𝟙 M`, so this is `hmap`
  have hsmulD : ∀ L : DerivedCategory AL,
      Φ.mapDerivedCategory.map (aL • 𝟙 L) = aW • 𝟙 (Φ.mapDerivedCategory.obj L) :=
    fun L => Stacks.SheafOfModules.DerivedRestrictScalars.mapDerivedCategory_map_smul_id
      Φ aL aW
      (fun Z => Stacks.SemilinearFunctor.map_smul_id_mapHomologicalComplex Φ aL aW
        (fun M => (congrArg Φ.map (Category.comp_id (aL.app M))).trans
          ((hmap M).trans (Category.comp_id (aW.app (Φ.obj M))).symm))
        (ComplexShape.up ℤ) Z) L
  -- restricting to `W.left` and transporting is restricting to `U` and then to `W`
  let i₁ := Stacks.SheafOfModules.DerivedRestrictScalars.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) W.left) Φ
  let i₂ := Stacks.SheafOfModules.DerivedRestrictScalars.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U)
    (SheafOfModules.overFunctor.{max u v} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U) W)
  exact (AlgebraicGeometry.RingedSite.isDerivedCompleteAt_iff_of_iso
      ((i₁.app K).symm ≪≫ i₂.app K) aW).mp
    (isDerivedCompleteAt_map_of_smul_id Φ.mapDerivedCategory (hsmulD _) hKW)

/-- **Derived completeness is preserved by restriction to a localized ringed site**, the first
step of [Stacks, Tag 0A0F]. If `K` is derived complete along a sheaf of ideals `ℐ ⊂ 𝒪` on a ringed
site `(𝒞, 𝒪)`, then for every object `U` the restriction `K|_U` is derived complete along the
restriction `ℐ|_U` of `ℐ` to the localized ringed site `(𝒞/U, 𝒪_U)`.

This is `AlgebraicGeometry.RingedSite.restrict_isDerivedComplete` at the restricted sheaf of
ideals `AlgebraicGeometry.RingedSite.overIdeal`, whose sections over `V` are by definition the
sections of `ℐ` over `V.left`. -/
theorem restrict_isDerivedComplete_overIdeal
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) (U : X.C)
    (K : DerivedCategory (SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hK : IsDerivedComplete.{u, v, max u v, max u v} X I K) :
    let F := SheafOfModules.overFunctor.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U
    ∃ hAdd : F.Additive,
    ∃ hLim : PreservesFiniteLimits F,
    ∃ hColim : PreservesFiniteColimits F,
      letI : F.Additive := hAdd
      letI : PreservesFiniteLimits F := hLim
      letI : PreservesFiniteColimits F := hColim
      IsDerivedComplete.{max u v, v, max u v, max u v} (X.over U) (overIdeal I U)
        (F.mapDerivedCategory.obj K) :=
  restrict_isDerivedComplete X I U (overIdeal I U) (fun _ _ hg => hg) K hK

end Derived

end AlgebraicGeometry.RingedSite

end
