module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Restriction
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorAlongAComposite

/-!
# The head of the join: the unit of a restricted morphism against the unit itself

`OrdinaryTopDegreeMate.lean` puts the γ side of conclusion (c) of [Stacks, Tag 0EX3] in the shape
`R^d f'_*(η) ≫ Θ`, with `η` the ordinary unit of `(h')^* ⊣ (h')_*` of [Stacks, Tag 0096]. The (A)
side over a compatible pair of affine opens is, by
`…TopDegreeBaseChange.affineOpenCohomologyPullbackMap_eq_sections_rightDerivedPlus_unit`, the
sections over `V` of `R^d (f' ∣_ V)_*` of the unit of the **restricted** adjunction. This file
proves the head-side matching of the two, so that the join is a composition of two proved halves
rather than one declaration carrying everything.

## Main results

* `…TopDegreeBaseChange.unit_restrictPullback_eq_unit_pullbackRestrict`: the adjoint
  characterisation of `AffinePushforward.pullbackRestrictIso` with both composite adjunctions
  unfolded, which is the relation between the unit of `f` and the unit of `f ∣_ V`.
* `…TopDegreeBaseChange.presheaf_map_comp_comp`: three restriction maps of one module compose to
  the single restriction map between the two ends, opens being a poset.
* `…TopDegreeBaseChange.pushforwardComp_pushforwardCongr_naturality`: **the reconciliation of
  `(V.ι)_* ∘ (f ∣_ V)_*` with `((f ⁻¹ᵁ V).ι ≫ f)_*`**, which is the naturality of the composite
  of the two canonical comparisons.
* `…TopDegreeBaseChange.restrictUnit_comp_restrictPushforwardIso_hom`: **the restriction unit of
  `V` followed by `AffinePushforward.restrictPushforwardIso` and those two comparisons is the
  direct image along `f` of the restriction unit of `f ⁻¹ᵁ V`**, both sides being restriction
  maps of the module between the same two opens.
* `…TopDegreeBaseChange.map_unit_comp_pullbackRestrictIso_eq_unit`: **the transposition.** The
  restriction to `V` of the unit of `f^* ⊣ f_*`, carried across
  `AffinePushforward.restrictPushforwardIso` and `AffinePushforward.pullbackRestrictIso`, is the
  unit of `(f ∣_ V)^* ⊣ (f ∣_ V)_*`.
* `…TopDegreeBaseChange.rightDerivedPlusRestrictObjIso_hom_naturality_unit`:
  `…SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso_hom_naturality` read at the ordinary
  unit of `(h')^* ⊣ (h')_*`, in the ringed-space spelling the γ side carries that unit in.
* `…TopDegreeBaseChange.modulePullbackComp_unit_resLE`:
  `Stacks.PullbackTensorComposition.modulePullbackComp_unit` read at the factorisation
  `Stacks.AlgebraicGeometry.RestrictionSections.resLE_toShHom`, which is the unit of
  `k^* ⊣ k_*` for `k` a morphism restricted to a compatible pair of opens, at morphism level.
* `…TopDegreeBaseChange.unit_resLE_eq_unit_morphismRestrict`: the same identity solved for the
  unit of `k^* ⊣ k_*` and with the composite unit expanded, so that what stands first is the
  unit of `(h ∣_ U)^* ⊣ (h ∣_ U)_*`.
* `…TopDegreeBaseChange.unit_resLE_eq_restrictFunctor_map_unit`: **the unit of `k^* ⊣ k_*` at a
  restricted module is the restriction of the unit of `h^* ⊣ h_*`**, followed by five named
  comparisons: the previous result with the transposition substituted into it.
* `…TopDegreeBaseChange.rightDerivedPlus_map_restrictFunctor_map_unit`:
  `rightDerivedPlusRestrictObjIso_hom_naturality_unit` solved for its left edge.
* `…TopDegreeBaseChange.rightDerivedPlus_map_unit_resLE`: **the head matching of conclusion (c)
  of [Stacks, Tag 0EX3].** `R^p (f' ∣_ V)_*` of the unit of `k^* ⊣ k_*` — the (A) side — is
  `R^p f'_*` of the ordinary unit of `(h')^* ⊣ (h')_*` restricted to `V` — the γ side —
  conjugated by [Stacks, Tag 01E5] and followed by the higher direct image of those five
  comparisons.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

/-- **The unit of `f ∣_ V` against the unit of `f`.**
`Stacks.Conormal.Restriction.unit_comp_map_pullbackRestrictIso_hom_app` is the adjoint
characterisation of `AffinePushforward.pullbackRestrictIso`, stated at two composite adjunctions;
this is the same identity with both composites unfolded by
`CategoryTheory.Adjunction.comp_unit_app` and `CategoryTheory.Adjunction.ofNatIsoRight_unit`, so
that what appears is the unit of `f^* ⊣ f_*` on one side and the unit of `(f ∣_ V)^* ⊣ (f ∣_ V)_*`
on the other.

This is the step that carries the ordinary unit of [Stacks, Tag 0096] from `X` down to the open
subscheme `f⁻¹(V)`; no hypothesis is placed on `f`, on `V` or on `M`. -/
theorem unit_restrictPullback_eq_unit_pullbackRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    (V : S.Opens) (M : S.Modules) :
    (Scheme.Modules.restrictAdjunction V.ι).unit.app M ≫
        (Scheme.Modules.pushforward V.ι).map
            ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ V)).unit.app
              ((Scheme.Modules.restrictFunctor V.ι).obj M)) ≫
          (Scheme.Modules.pushforwardComp (f ∣_ V) V.ι).hom.app
              ((Scheme.Modules.pullback (f ∣_ V)).obj
                ((Scheme.Modules.restrictFunctor V.ι).obj M)) ≫
            (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f V)).hom.app
              ((Scheme.Modules.pullback (f ∣_ V)).obj
                ((Scheme.Modules.restrictFunctor V.ι).obj M)) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map
            ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app
              ((Scheme.Modules.pullback f).obj M)) ≫
          (Scheme.Modules.pushforwardComp (f ⁻¹ᵁ V).ι f).hom.app
              ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj
                ((Scheme.Modules.pullback f).obj M)) ≫
            (Scheme.Modules.pushforward ((f ⁻¹ᵁ V).ι ≫ f)).map
              ((AffinePushforward.pullbackRestrictIso f V).hom.app M) := by
  simpa [AffinePushforward.pullbackRestrictAdjunction,
    AffinePushforward.restrictPullbackAdjunction, Adjunction.ofNatIsoRight_unit,
    Adjunction.comp_unit_app, Category.assoc] using
    (Stacks.Conormal.Restriction.unit_comp_map_pullbackRestrictIso_hom_app f V M).symm

/-! ### The reconciliation of the two iterated direct images -/

/-- Three restriction maps of one sheaf of modules, along morphisms of opens of its scheme,
compose to the single restriction map between the two ends. The opens of a scheme form a poset,
so there is nothing to choose between two morphisms with the same source and target, and the
identity is `CategoryTheory.Functor.map_comp` twice followed by `Subsingleton.elim`.

It is stated at variables, with the fourth morphism given rather than built, because the
consumer below meets each of the three factors in a different spelling: a restriction unit, a
component of `AffinePushforward.restrictPushforwardIso` and a component of
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr`. Those spellings are definitionally
restriction maps, so one application of this lemma reconciles them with no rewrite. -/
theorem presheaf_map_comp_comp {X : Scheme.{u}} (N : X.Modules) {U₁ U₂ U₃ U₄ : X.Opens}
    (i : U₂ ⟶ U₁) (j : U₃ ⟶ U₂) (k : U₄ ⟶ U₃) (l : U₄ ⟶ U₁) :
    N.presheaf.map i.op ≫ N.presheaf.map j.op ≫ N.presheaf.map k.op =
      N.presheaf.map l.op := by
  have h : i.op ≫ j.op ≫ k.op = l.op := Subsingleton.elim _ _
  rw [← Functor.map_comp, ← Functor.map_comp, h]

/-- **The reconciliation of `(V.ι)_* ∘ (f ∣_ V)_*` with `((f ⁻¹ᵁ V).ι ≫ f)_*`.** The two
iterated direct images are compared by `AlgebraicGeometry.Scheme.Modules.pushforwardComp`
followed by `AlgebraicGeometry.Scheme.Modules.pushforwardCongr` at
`AlgebraicGeometry.morphismRestrict_ι`, and this is the naturality of that composite: a morphism
of modules on `f ⁻¹ᵁ V` may be pushed forward in two steps and then compared, or compared and
then pushed forward along the composite.

Both comparisons are natural transformations, so this is `CategoryTheory.NatTrans.naturality`
twice. It is isolated because the matching of the two sides of conclusion (c) of
[Stacks, Tag 0EX3] has to carry `AffinePushforward.pullbackRestrictIso` across it. -/
@[reassoc]
theorem pushforwardComp_pushforwardCongr_naturality {X S : Scheme.{u}} (f : X ⟶ S)
    (V : S.Opens) {N₁ N₂ : (f ⁻¹ᵁ V).toScheme.Modules} (g : N₁ ⟶ N₂) :
    (Scheme.Modules.pushforward V.ι).map ((Scheme.Modules.pushforward (f ∣_ V)).map g) ≫
        (Scheme.Modules.pushforwardComp (f ∣_ V) V.ι).hom.app N₂ ≫
          (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f V)).hom.app N₂ =
      (Scheme.Modules.pushforwardComp (f ∣_ V) V.ι).hom.app N₁ ≫
        (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f V)).hom.app N₁ ≫
          (Scheme.Modules.pushforward ((f ⁻¹ᵁ V).ι ≫ f)).map g := by
  refine Eq.trans ((Scheme.Modules.pushforwardComp (f ∣_ V) V.ι).hom.naturality_assoc g _) ?_
  exact congrArg (fun z => (Scheme.Modules.pushforwardComp (f ∣_ V) V.ι).hom.app N₁ ≫ z)
    ((Scheme.Modules.pushforwardCongr (morphismRestrict_ι f V)).hom.naturality g)

/-- **The two restriction units against `AffinePushforward.restrictPushforwardIso`.** The unit of
`restrictFunctor V.ι ⊣ (V.ι)_*` at `f_* N`, followed by `(V.ι)_*` of the comparison of the
restricted direct image with the direct image of the restriction and then by the reconciliation
of the two iterated direct images, is the direct image along `f` of the unit of
`restrictFunctor (f ⁻¹ᵁ V).ι ⊣ ((f ⁻¹ᵁ V).ι)_*` at `N`, followed by
`AlgebraicGeometry.Scheme.Modules.pushforwardComp`.

Every factor is, on sections over an open `W` of `S`, a restriction map of `N` itself:
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`,
`Stacks.Conormal.Restriction.restrictPushforwardIso_hom_app`,
`AlgebraicGeometry.Scheme.Modules.pushforwardComp_hom_app_app` and
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr_hom_app_app` are all `rfl`. Both sides
therefore run between the same two opens of `X`, and `presheaf_map_comp_comp` identifies them.
There is no hypothesis on `f`, on `V` or on `N`. -/
@[reassoc]
theorem restrictUnit_comp_restrictPushforwardIso_hom {X S : Scheme.{u}} (f : X ⟶ S)
    (V : S.Opens) (N : X.Modules) :
    (Scheme.Modules.restrictAdjunction V.ι).unit.app ((Scheme.Modules.pushforward f).obj N) ≫
        (Scheme.Modules.pushforward V.ι).map
            ((AffinePushforward.restrictPushforwardIso f V).hom.app N) ≫
          (Scheme.Modules.pushforwardComp (f ∣_ V) V.ι).hom.app
              ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj N) ≫
            (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f V)).hom.app
              ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj N) =
      (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι).unit.app N) ≫
        (Scheme.Modules.pushforwardComp (f ⁻¹ᵁ V).ι f).hom.app
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj N) := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  exact presheaf_map_comp_comp N
    (homOfLE (show f ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ W)) ≤ f ⁻¹ᵁ W from
      fun z hz => V.ι.image_preimage_le W hz))
    (eqToHom (image_morphismRestrict_preimage f V (V.ι ⁻¹ᵁ W)))
    (homOfLE (le_of_eq (show (f ⁻¹ᵁ V).ι ''ᵁ (((f ⁻¹ᵁ V).ι ≫ f) ⁻¹ᵁ W) =
      (f ⁻¹ᵁ V).ι ''ᵁ ((f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ W)) from by rw [← morphismRestrict_ι f V]; rfl)))
    (homOfLE (show (f ⁻¹ᵁ V).ι ''ᵁ (((f ⁻¹ᵁ V).ι ≫ f) ⁻¹ᵁ W) ≤ f ⁻¹ᵁ W from
      fun z hz => (f ⁻¹ᵁ V).ι.image_preimage_le (f ⁻¹ᵁ W) hz))

/-! ### The transposition -/

/-- **The restriction to `V` of the unit of `f^* ⊣ f_*` is the unit of
`(f ∣_ V)^* ⊣ (f ∣_ V)_*`.** Carrying the restricted unit across the comparison of the restricted
direct image with the direct image of the restriction
(`AffinePushforward.restrictPushforwardIso`) and then across the comparison of the restricted
inverse image with the inverse image of the restriction
(`AffinePushforward.pullbackRestrictIso`) gives exactly the unit of the restricted adjunction.

This is the head-side matching of conclusion (c) of [Stacks, Tag 0EX3]: the γ side carries the
unit of `(h')^* ⊣ (h')_*` on `X'`, the (A) side over an affine open `V` carries the unit of the
adjunction restricted over `f'⁻¹(V)`, and this identity is what turns the one into the other.

The proof transposes along `restrictFunctor V.ι ⊣ (V.ι)_*`, where
`CategoryTheory.Adjunction.unit_naturality` removes the restriction functor, and then composes
`unit_restrictPullback_eq_unit_pullbackRestrict` — the adjoint characterisation of
`AffinePushforward.pullbackRestrictIso` — with `restrictUnit_comp_restrictPushforwardIso_hom` and
`pushforwardComp_pushforwardCongr_naturality`, the two comparisons of iterated direct images
being isomorphisms. No hypothesis is placed on `f`, on `V` or on `M`. -/
theorem map_unit_comp_pullbackRestrictIso_eq_unit {X S : Scheme.{u}} (f : X ⟶ S)
    (V : S.Opens) (M : S.Modules) :
    (Scheme.Modules.restrictFunctor V.ι).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        (AffinePushforward.restrictPushforwardIso f V).hom.app
            ((Scheme.Modules.pullback f).obj M) ≫
          (Scheme.Modules.pushforward (f ∣_ V)).map
            ((AffinePushforward.pullbackRestrictIso f V).hom.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ V)).unit.app
        ((Scheme.Modules.restrictFunctor V.ι).obj M) := by
  apply ((Scheme.Modules.restrictAdjunction V.ι).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.unit_naturality, Functor.comp_obj, Functor.id_obj]
  rw [← cancel_mono ((Scheme.Modules.pushforwardComp (f ∣_ V) V.ι).hom.app
        ((Scheme.Modules.pullback (f ∣_ V)).obj ((Scheme.Modules.restrictFunctor V.ι).obj M)) ≫
      (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f V)).hom.app
        ((Scheme.Modules.pullback (f ∣_ V)).obj ((Scheme.Modules.restrictFunctor V.ι).obj M)))]
  simp only [Category.assoc]
  rw [pushforwardComp_pushforwardCongr_naturality,
    restrictUnit_comp_restrictPushforwardIso_hom_assoc,
    unit_restrictPullback_eq_unit_pullbackRestrict]

/-! ### The restriction comparison of the higher direct images, at the ordinary unit -/

attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks, Tag 01E5] for the higher direct images, read at the ordinary unit of
`(h')^* ⊣ (h')_*`.**
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso_hom_naturality`
is the naturality in the module of the comparison between `R^p (f' ∣_ V)_*` of a restriction and
the restriction of `R^p f'_*`; this is its component at the unit of [Stacks, Tag 0096], which is
the morphism the γ side of conclusion (c) of [Stacks, Tag 0EX3] carries.

The unit is spelled at `RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction`, the
spelling the γ side has it in, while the derived functors and the comparison are spelled at
`AlgebraicGeometry.Scheme.Modules`. The two vocabularies are the same data —
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.category_modules_eq_category_sheafOfModules`
is `rfl` — but not to instance search, so this declaration performs that crossing once, in
argument position and alongside nothing else.

*The identity functor is left standing in the statement.* The source of a unit is
`(𝟭 _).obj F'`, and replacing it by `F'` — true by `rfl` — makes the kernel unfold
`…SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` under the `rightDerivedPlus` of this
file's measurement, which is a deterministic timeout. Written as the application produces it,
the declaration checks in a fraction of a second. -/
theorem rightDerivedPlusRestrictObjIso_hom_naturality_unit {X' Y' X'' : Scheme.{u}}
    (f' : X' ⟶ Y') (h' : X'' ⟶ X') (V : Y'.Opens) (p : ℕ) (F' : X'.Modules) :
    ((Scheme.Modules.pushforward (f' ∣_ V)).rightDerivedPlus (p : ℤ)).map
          ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).map
            ((modulePullbackPushforwardAdjunction h'.toLRSHom.toShHom).unit.app F')) ≫
        (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f' V p
            ((modulePullback h'.toLRSHom.toShHom ⋙
              modulePushforward h'.toLRSHom.toShHom).obj F')).hom =
      (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f' V p
            ((𝟭 (SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace))).obj F')).hom ≫
        (Scheme.Modules.restrictFunctor V.ι).map
          (((Scheme.Modules.pushforward f').rightDerivedPlus (p : ℤ)).map
            ((modulePullbackPushforwardAdjunction h'.toLRSHom.toShHom).unit.app F')) :=
  SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso_hom_naturality f' V p
    ((modulePullbackPushforwardAdjunction h'.toLRSHom.toShHom).unit.app F')

/-- **The unit of `k^* ⊣ k_*` for `k` a morphism restricted to a compatible pair of opens.**
Let `h : X ⟶ Y`, let `U` be an open of `Y`, let `V` be an open of `X` with `V ≤ h⁻¹(U)` and write
`k := h.resLE U V e`. Then the unit of `k^* ⊣ k_*`, followed by the comparison of the two
iterated direct images, is the unit of the composite adjunction followed by the direct image of
the composition law for pullback.

`AlgebraicGeometry.Scheme.Hom.resLE` is `X.homOfLE e ≫ h ∣_ U` and a composite of morphisms of
schemes is the composite of the underlying morphisms of ringed spaces, so this is
`Stacks.PullbackTensorComposition.modulePullbackComp_unit` at the factorisation
`Stacks.AlgebraicGeometry.RestrictionSections.resLE_toShHom`, with no transport between the two
spellings of `k`. It is the morphism-level companion of
`Stacks.AlgebraicGeometry.RestrictionSections.pullbackUnit_resLE`, which reads the same identity
on sections, and it is the form a consumer that has to apply `R^d (f' ∣_ V)_*` to the unit needs.
There is no hypothesis on `h`, on the two opens or on `M`. -/
theorem modulePullbackComp_unit_resLE {X Y : Scheme.{u}} (h : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ h ⁻¹ᵁ U)
    (M : SheafOfModules.{u} (structureSheafRing U.toScheme.toSheafedSpace)) :
    (modulePullbackPushforwardAdjunction (h.resLE U V e).toLRSHom.toShHom).unit.app M ≫
        (modulePushforwardComp (X.homOfLE e).toLRSHom.toShHom
            (h ∣_ U).toLRSHom.toShHom).inv.app
          ((modulePullback (h.resLE U V e).toLRSHom.toShHom).obj M) =
      ((modulePullbackPushforwardAdjunction (h ∣_ U).toLRSHom.toShHom).comp
            (modulePullbackPushforwardAdjunction (X.homOfLE e).toLRSHom.toShHom)).unit.app M ≫
        (modulePushforward (X.homOfLE e).toLRSHom.toShHom ⋙
            modulePushforward (h ∣_ U).toLRSHom.toShHom).map
          ((Stacks.DerivedPullback.Composition.modulePullbackComp
            (X.homOfLE e).toLRSHom.toShHom (h ∣_ U).toLRSHom.toShHom).hom.app M) :=
  Stacks.PullbackTensorComposition.modulePullbackComp_unit
    (X.homOfLE e).toLRSHom.toShHom (h ∣_ U).toLRSHom.toShHom M

/-! ### The head matching -/

/-- **The unit of `k^* ⊣ k_*`, `k := h.resLE U V e`, split into its two legs.**
`modulePullbackComp_unit_resLE` with the composite unit expanded by
`CategoryTheory.Adjunction.comp_unit_app` and the comparison of the two iterated direct images
carried to the other side, the comparison being an isomorphism: the unit of `k^* ⊣ k_*` is the
unit of `(h ∣_ U)^* ⊣ (h ∣_ U)_*`, then the direct image along `h ∣_ U` of the unit of the open
immersion `X.homOfLE e`, then the two composition laws.

It is stated at a module `M` of the `SheafOfModules (structureSheafRing …)` spelling — the
spelling `modulePullbackComp_unit_resLE` is in — and at no restriction, so that the whole
identity lives in one vocabulary; the consumer below instantiates `M` at a restriction, which
is where the two vocabularies meet. There is no hypothesis on `h`, on the two opens or on
`M`. -/
theorem unit_resLE_eq_unit_morphismRestrict {X Y : Scheme.{u}} (h : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ h ⁻¹ᵁ U)
    (M : SheafOfModules.{u} (structureSheafRing U.toScheme.toSheafedSpace)) :
    (modulePullbackPushforwardAdjunction (h.resLE U V e).toLRSHom.toShHom).unit.app M =
      (modulePullbackPushforwardAdjunction (h ∣_ U).toLRSHom.toShHom).unit.app M ≫
        (modulePushforward (h ∣_ U).toLRSHom.toShHom).map
            ((modulePullbackPushforwardAdjunction (X.homOfLE e).toLRSHom.toShHom).unit.app
              ((modulePullback (h ∣_ U).toLRSHom.toShHom).obj M)) ≫
          (modulePushforward (X.homOfLE e).toLRSHom.toShHom ⋙
                modulePushforward (h ∣_ U).toLRSHom.toShHom).map
              ((Stacks.DerivedPullback.Composition.modulePullbackComp
                (X.homOfLE e).toLRSHom.toShHom (h ∣_ U).toLRSHom.toShHom).hom.app M) ≫
            (modulePushforwardComp (X.homOfLE e).toLRSHom.toShHom
                (h ∣_ U).toLRSHom.toShHom).hom.app
              ((modulePullback (h.resLE U V e).toLRSHom.toShHom).obj M) := by
  have hk := modulePullbackComp_unit_resLE h e M
  rw [Adjunction.comp_unit_app] at hk
  exact ((Iso.comp_inv_eq ((modulePushforwardComp (X.homOfLE e).toLRSHom.toShHom
          (h ∣_ U).toLRSHom.toShHom).app
        ((modulePullback (h.resLE U V e).toLRSHom.toShHom).obj M))).mp hk).trans
    ((Category.assoc _ _ _).trans (Category.assoc _ _ _))

/-- **The unit of `k^* ⊣ k_*` at a restricted module, in terms of the unit of `h^* ⊣ h_*`.**
Let `h : X'' ⟶ X'`, let `U` be an open of `X'`, let `W'` be an open of `X''` with
`W' ≤ h⁻¹(U)` and write `k := h.resLE U W' e`. Then the unit of `k^* ⊣ k_*` at the restriction
to `U` of a module `F'` on `X'` is the restriction to `U` of the unit of `h^* ⊣ h_*` at `F'`,
followed by five named comparisons and no hypothesis-bearing step.

This is `unit_resLE_eq_unit_morphismRestrict` at the restriction of `F'`, with its leading unit
of `(h ∣_ U)^* ⊣ (h ∣_ U)_*` replaced by `map_unit_comp_pullbackRestrictIso_eq_unit`, the
transposition. No hypothesis is placed on `h`, on the two opens or on `F'`.

The two vocabularies meet here: the transposition is stated at
`AlgebraicGeometry.Scheme.Modules` and the composition law for pullback at
`SheafOfModules (structureSheafRing …)`. They are the same data, so each crossing happens in
argument position and costs a definitional unfolding, not a transport. -/
theorem unit_resLE_eq_restrictFunctor_map_unit {X' X'' : Scheme.{u}} (h' : X'' ⟶ X')
    {U : X'.Opens} {W' : X''.Opens} (e : W' ≤ h' ⁻¹ᵁ U) (F' : X'.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (h'.resLE U W' e)).unit.app
        ((Scheme.Modules.restrictFunctor U.ι).obj F') =
      (Scheme.Modules.restrictFunctor U.ι).map
          ((modulePullbackPushforwardAdjunction h'.toLRSHom.toShHom).unit.app F') ≫
        (AffinePushforward.restrictPushforwardIso h' U).hom.app
            ((Scheme.Modules.pullback h').obj F') ≫
          (Scheme.Modules.pushforward (h' ∣_ U)).map
              ((AffinePushforward.pullbackRestrictIso h' U).hom.app F') ≫
            (modulePushforward (h' ∣_ U).toLRSHom.toShHom).map
                ((modulePullbackPushforwardAdjunction
                      (X''.homOfLE e).toLRSHom.toShHom).unit.app
                  ((modulePullback (h' ∣_ U).toLRSHom.toShHom).obj
                    ((Scheme.Modules.restrictFunctor U.ι).obj F'))) ≫
              (modulePushforward (X''.homOfLE e).toLRSHom.toShHom ⋙
                    modulePushforward (h' ∣_ U).toLRSHom.toShHom).map
                  ((Stacks.DerivedPullback.Composition.modulePullbackComp
                      (X''.homOfLE e).toLRSHom.toShHom
                      (h' ∣_ U).toLRSHom.toShHom).hom.app
                    ((Scheme.Modules.restrictFunctor U.ι).obj F')) ≫
                (modulePushforwardComp (X''.homOfLE e).toLRSHom.toShHom
                      (h' ∣_ U).toLRSHom.toShHom).hom.app
                  ((modulePullback (h'.resLE U W' e).toLRSHom.toShHom).obj
                    ((Scheme.Modules.restrictFunctor U.ι).obj F')) := by
  have h1 : ((Scheme.Modules.restrictFunctor U.ι).map
        ((modulePullbackPushforwardAdjunction h'.toLRSHom.toShHom).unit.app F') ≫
      (AffinePushforward.restrictPushforwardIso h' U).hom.app
          ((Scheme.Modules.pullback h').obj F')) ≫
        (Scheme.Modules.pushforward (h' ∣_ U)).map
          ((AffinePushforward.pullbackRestrictIso h' U).hom.app F') =
      (modulePullbackPushforwardAdjunction (h' ∣_ U).toLRSHom.toShHom).unit.app
        ((Scheme.Modules.restrictFunctor U.ι).obj F') :=
    (Category.assoc _ _ _).trans (map_unit_comp_pullbackRestrictIso_eq_unit h' U F')
  exact (unit_resLE_eq_unit_morphismRestrict h' e
      ((Scheme.Modules.restrictFunctor U.ι).obj F')).trans
    ((congrArg (fun z => z ≫ _) h1.symm).trans
      ((Category.assoc _ _ _).trans (Category.assoc _ _ _)))

/-- **[Stacks, Tag 01E5] solved for the restricted higher direct image of the ordinary unit.**
`rightDerivedPlusRestrictObjIso_hom_naturality_unit` is a commuting square; this is that square
read as a formula for its left edge, the comparison being an isomorphism. It is the form the
head matching consumes, because there the restricted higher direct image of the unit occurs
alone and has to be replaced.

*The identity functor is left standing*, for the reason recorded at
`rightDerivedPlusRestrictObjIso_hom_naturality_unit`: replacing `(𝟭 _).obj F'` by `F'` is true
by `rfl` and makes the kernel unfold the comparison underneath `rightDerivedPlus`. -/
theorem rightDerivedPlus_map_restrictFunctor_map_unit {X' Y' X'' : Scheme.{u}}
    (f' : X' ⟶ Y') (h' : X'' ⟶ X') (V : Y'.Opens) (p : ℕ) (F' : X'.Modules) :
    ((Scheme.Modules.pushforward (f' ∣_ V)).rightDerivedPlus (p : ℤ)).map
        ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).map
          ((modulePullbackPushforwardAdjunction h'.toLRSHom.toShHom).unit.app F')) =
      (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f' V p
            ((𝟭 (SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace))).obj F')).hom ≫
        (Scheme.Modules.restrictFunctor V.ι).map
            (((Scheme.Modules.pushforward f').rightDerivedPlus (p : ℤ)).map
              ((modulePullbackPushforwardAdjunction h'.toLRSHom.toShHom).unit.app F')) ≫
          (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f' V p
              ((modulePullback h'.toLRSHom.toShHom ⋙
                modulePushforward h'.toLRSHom.toShHom).obj F')).inv := by
  rw [← Category.assoc, ← rightDerivedPlusRestrictObjIso_hom_naturality_unit, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- **The head matching of conclusion (c) of [Stacks, Tag 0EX3].** The degree-`p` higher direct
image along `f' ∣_ V` of the unit of `k^* ⊣ k_*`, `k := h'.resLE (f'⁻¹V) W' e` — which is what
the (A) side of (c) carries over a compatible pair of opens, by
`…TopDegreeBaseChange.affineOpenCohomologyPullbackMap_eq_sections_rightDerivedPlus_unit` — is
the restriction to `V` of the degree-`p` higher direct image along `f'` of the ordinary unit of
`(h')^* ⊣ (h')_*` — which is what the γ side carries, by
`…TopDegreeBaseChange.homEquiv_topDirectImageBaseChangeMapPlus_eq_rightDerivedPlus_unit` —
conjugated by [Stacks, Tag 01E5] at the two coefficients and followed by the higher direct
image of the five comparisons of `unit_resLE_eq_restrictFunctor_map_unit`.

Every factor on the right-hand side is a named comparison: the restriction comparison of the
higher direct images at the source and at the target, the restriction–direct-image comparison
`AffinePushforward.restrictPushforwardIso`, the restriction–inverse-image comparison
`AffinePushforward.pullbackRestrictIso`, the unit of the open immersion `X''.homOfLE e`, the
composition law for pullback and the composition law for pushforward. Nothing is an
`CategoryTheory.eqToHom`. No hypothesis is placed on `f'`, on `h'`, on `V`, on `W'` or on `F'`
beyond `e : W' ≤ h' ⁻¹ᵁ (f' ⁻¹ᵁ V)`; in particular neither morphism is assumed affine,
quasi-compact or quasi-separated, and `F'` is not assumed quasi-coherent.

The proof is `unit_resLE_eq_restrictFunctor_map_unit`, `CategoryTheory.Functor.map_comp` to
split the leading restricted unit off, and `rightDerivedPlus_map_restrictFunctor_map_unit` on
that leading factor. -/
theorem rightDerivedPlus_map_unit_resLE {X' Y' X'' : Scheme.{u}} (f' : X' ⟶ Y')
    (h' : X'' ⟶ X') (V : Y'.Opens) {W' : X''.Opens} (e : W' ≤ h' ⁻¹ᵁ (f' ⁻¹ᵁ V))
    (F' : X'.Modules) (p : ℕ) :
    ((Scheme.Modules.pushforward (f' ∣_ V)).rightDerivedPlus (p : ℤ)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (h'.resLE (f' ⁻¹ᵁ V) W' e)).unit.app
          ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')) =
      (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f' V p
            ((𝟭 (SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace))).obj F')).hom ≫
        (Scheme.Modules.restrictFunctor V.ι).map
            (((Scheme.Modules.pushforward f').rightDerivedPlus (p : ℤ)).map
              ((modulePullbackPushforwardAdjunction h'.toLRSHom.toShHom).unit.app F')) ≫
          (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f' V p
              ((modulePullback h'.toLRSHom.toShHom ⋙
                modulePushforward h'.toLRSHom.toShHom).obj F')).inv ≫
            ((Scheme.Modules.pushforward (f' ∣_ V)).rightDerivedPlus (p : ℤ)).map
              ((AffinePushforward.restrictPushforwardIso h' (f' ⁻¹ᵁ V)).hom.app
                  ((Scheme.Modules.pullback h').obj F') ≫
                (Scheme.Modules.pushforward (h' ∣_ (f' ⁻¹ᵁ V))).map
                    ((AffinePushforward.pullbackRestrictIso h' (f' ⁻¹ᵁ V)).hom.app F') ≫
                  (modulePushforward (h' ∣_ (f' ⁻¹ᵁ V)).toLRSHom.toShHom).map
                      ((modulePullbackPushforwardAdjunction
                            (X''.homOfLE e).toLRSHom.toShHom).unit.app
                        ((modulePullback (h' ∣_ (f' ⁻¹ᵁ V)).toLRSHom.toShHom).obj
                          ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F'))) ≫
                    (modulePushforward (X''.homOfLE e).toLRSHom.toShHom ⋙
                          modulePushforward (h' ∣_ (f' ⁻¹ᵁ V)).toLRSHom.toShHom).map
                        ((Stacks.DerivedPullback.Composition.modulePullbackComp
                            (X''.homOfLE e).toLRSHom.toShHom
                            (h' ∣_ (f' ⁻¹ᵁ V)).toLRSHom.toShHom).hom.app
                          ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')) ≫
                      (modulePushforwardComp (X''.homOfLE e).toLRSHom.toShHom
                            (h' ∣_ (f' ⁻¹ᵁ V)).toLRSHom.toShHom).hom.app
                        ((modulePullback
                            (h'.resLE (f' ⁻¹ᵁ V) W' e).toLRSHom.toShHom).obj
                          ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F'))) := by
  have h3 := (rightDerivedPlus_map_restrictFunctor_map_unit f' h' V p F').trans
    (Category.assoc _ _ _).symm
  exact (congrArg
        (fun z => ((Scheme.Modules.pushforward (f' ∣_ V)).rightDerivedPlus (p : ℤ)).map z)
      (unit_resLE_eq_restrictFunctor_map_unit h' e F')).trans
    ((Functor.map_comp _ _ _).trans
      ((congrArg (fun z => z ≫ _) h3).trans
        ((Category.assoc _ _ _).trans (Category.assoc _ _ _))))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
