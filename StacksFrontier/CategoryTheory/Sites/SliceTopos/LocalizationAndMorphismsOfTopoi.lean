module
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.InverseImage
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.OverPushforward
public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-! # Localizing a morphism of sites at an object, and the morphism of topoi at `h_V^#`

Let `u : C ⥤ D` be a continuous functor between the sites `(C, J)` and `(D, K)` defining a morphism
of sites, so that it induces a morphism of topoi `f : Sh(D) ⟶ Sh(C)` with `f⁻¹ = u_s` (Stacks
00XC).  Let `V` be an object of `C` and put `U = u V`.  (Stacks writes the morphism of sites as
`f : C → D` with the continuous functor running backwards, `u : D → C`; so Stacks' `C` is this
file's `D` and vice versa, and Stacks' `V ∈ Ob(D)`, `U = u(V) ∈ Ob(C)` are this file's `V : C` and
`U = u V : D`.)

There are two ways to localize `f`, and Stacks 04IU says they give the same morphism of topoi.
Localizing the *sites* (Stacks 03CF) uses that `u' = Over.post u : Over V ⥤ Over U` is again
continuous, and produces `f' : Sh(D/U) ⟶ Sh(C/V)` with `(f')⁻¹ = u'_s`.  Localizing the *topos*
(Stacks 04H1) is applied to the sheaf `G = h_V^#` on `C`, whose inverse image `f⁻¹G` is `h_U^#` by
Stacks 04D3, and produces `f'' : Sh(D)/f⁻¹G ⟶ Sh(C)/G` with `(f'')⁻¹ = Over.post f⁻¹`, i.e.
`(f'')⁻¹(H → h_V^#) = (f⁻¹H → f⁻¹h_V^#)`.  The two are compared through the equivalences
`Φ_V : Sh(C/V) ≌ Sh(C)/h_V^#` and `Φ_U : Sh(D/U) ≌ Sh(D)/h_U^#` of Stacks 00Y1, which by Stacks
04IQ identify the horizontal edges `j_F = j_U` and `j_G = j_V` of the two squares, together with
Stacks 04D3's identification `f⁻¹h_V^# ≅ h_U^#` of the two lower right corners.  So the assertion
of Stacks 04IU is that the square of functors
```
  (f')⁻¹ ⋙ Φ_U  ≅  Φ_V ⋙ (f'')⁻¹ ⋙ Over.map (04D3) : Sh(C/V) ⥤ Sh(D)/h_U^#
```
commutes; the pushforwards then agree by uniqueness of right adjoints, so the two morphisms of
topoi, and with the identifications of Stacks 04IQ the two diagrams, are the same.

After `Over.forget h_U^#` the two functors above are `j_{U!}(f')⁻¹` and `f⁻¹j_{V!}`, and these are
*canonically* isomorphic: that isomorphism is the displayed computation in the proof of Stacks
03CF, which comes from `f'_*j_U^{-1} = j_V^{-1}f_*` by uniqueness of left adjoints, read through
Stacks 00Y1; it is `CategoryTheory.SliceTopos.underlyingIso` and needs no exactness.  Since
`Over.forget` is faithful but not full, all that is left of Stacks 04IU is that this canonical
isomorphism respects the two structure maps to `h_U^#`, the right-hand one computed with Stacks
04D3's identification — one equation, stated here.  This is the "not a complete triviality" of the
source's proof: the isomorphism exists for free, and the content is that it is compatible with the
identification `f⁻¹h_V^# = h_U^#` that both constructions silently use.

## Main results

* `CategoryTheory.SliceTopos.underlyingIso_hom_app_comp_hom` (Stacks 04IU): the canonical
  isomorphism `j_{U!}(f')⁻¹ ≅ f⁻¹j_{V!}` of the proof of Stacks 03CF is an isomorphism over
  `h_U^#`, the structure map on the right being computed with Stacks 04D3's identification
  `f⁻¹h_V^# ≅ h_U^#`.  Equivalently, by `CategoryTheory.Over.natIsoOfForgetIso`, the localization
  of the morphism of sites at `V` agrees with the localization of the morphism of topoi at `h_V^#`.

## Implementation notes

The conclusion is one equation of morphisms rather than an isomorphism of functors, because that is
the whole content and because it is the form the library consumes: `Over.natIsoOfForgetIso` turns
it, together with the naturality that `underlyingIso` already carries, into the isomorphism
`(f')⁻¹ ⋙ Φ_U ≅ Φ_V ⋙ (f'')⁻¹ ⋙ Over.map (04D3)` displayed above, which is the agreement of the
two diagrams; an existence statement about that isomorphism would be weaker, since an arbitrary
isomorphism of those two functors says nothing about the identifications being used.  Only the
identification of the two `f'`s is asserted here: the horizontal edges of the two squares are
identified by Stacks 04IQ
(`CategoryTheory.OverShriek.overPullbackCompSheafFunctorToOverIso` and its companions).

The hypotheses are Stacks 04IU's own: `u` is continuous and `hu : u.IsMorphismOfSites J K` is the
"morphism of sites" of the statement (Stacks 00X1), which is what supplies the morphism of topoi
whose localization at `h_V^#` is one of the two sides.  Stacks 03EF's sufficient condition — `C`
has finite limits and `u` is left exact — is *not* assumed: it is strictly stronger, and every
ingredient of the proof below is available without it.  `Over.post u` is continuous whenever `u`
is (`Functor.isContinuous_overPost_of_isContinuous`, taken here as a `local instance` in place of
the 03EF-flavoured global instance `Functor.isContinuous_overPost_of_preservesFiniteLimits`), so
Stacks 03CF's clauses (b), (c), (d) and `CategoryTheory.SliceTopos.underlyingIso` hold with
`u.IsContinuous J K` alone, and so does Stacks 04D3's `sheafPullbackSheafifyYonedaIso`.

Faithfulness, on the four points a reader should check against the source.  (1) No hypothesis is
dead: `hu` provides the morphism of topoi `f` whose localization at `h_V^#` is one of the two
sides, and `V` is the object being localized at.  (2) The sites are the source's: `(C, J)` and
`(D, K)` are given, the slices carry the localized topologies `J.over V` and `K.over U` induced by
them, and the sheaves are sheaves of sets, as in the source.  (3) Every map is pinned, none merely
asserted to exist: the comparison is `underlyingIso`, the isomorphism of the proof of Stacks 03CF;
the identification of the corners is Stacks 04D3's `sheafPullbackSheafifyYonedaIso`, not an
unspecified one — this is the whole point of the lemma; and the two localizations are
`MorphismOfTopoi.over` (Stacks 04H1) and `Functor.sheafPullback` along `Over.post u` (Stacks 03CF).
(4) The instantiation is not degenerate: take `u = 𝟭 C` with `K = J`, where `Φ_U = Φ_V`, both
`(f')⁻¹` are the identity, and the equation says that Stacks 04D3's identification of `h_V^#` with
itself is the identity.

## References

Stacks Project, tag 04IU (`sites-lemma-localize-morphism-topoi-compare`); the two diagrams compared
are those of tag 04H1 and tag 03CF, the identifications are tag 04IQ (`j_F = j_U`) and tag 04D3
(`f⁻¹h_V^# = h_U^#`).

* [Stacks 04IU](https://stacks.math.columbia.edu/tag/04IU)
-/

namespace CategoryTheory.SliceTopos

section

universe u
open CategoryTheory Limits
open OverShriek
open CategoryTheory Limits Opposite CategoryTheory.SliceTopos CategoryTheory.OverShriek

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

namespace Stacks.SliceTopos.LocalizationCompare

/-- **The bijection of the sheafification adjunction** is `toSheafify` followed by the underlying
map. -/
private lemma sheafificationAdjunction_homEquiv_apply' {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (X : Cᵒᵖ ⥤ Type u) (Y : Sheaf J (Type u))
    (g : (presheafToSheaf J (Type u)).obj X ⟶ Y) :
    (sheafificationAdjunction J (Type u)).homEquiv X Y g = toSheafify J X ≫ g.hom := by
  rfl

/-- **The bijection of an adjunction composed after sheafification** is the sheafification map
followed by the underlying map of the second bijection. -/
private lemma sheafificationAdjunction_comp_homEquiv_apply {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) {E : Type*} [Category E] {P : Sheaf J (Type u) ⥤ E}
    {Q : E ⥤ Sheaf J (Type u)} (adj : P ⊣ Q) (X : Cᵒᵖ ⥤ Type u) (Y : E)
    (t : (presheafToSheaf J (Type u) ⋙ P).obj X ⟶ Y) :
    ((sheafificationAdjunction J (Type u)).comp adj).homEquiv X Y t =
      toSheafify J X ≫ (adj.homEquiv ((presheafToSheaf J (Type u)).obj X) Y t).hom := by
  rw [Adjunction.comp_homEquiv_apply, sheafificationAdjunction_homEquiv_apply']

/-- **The bijection of `OverShriek.presheafAdjunction` is `OverShriek.toRestricted`**: the
projection lemma that `presheafAdjunction`, being built by `Adjunction.mkOfHomEquiv`, does not
come with. -/
private lemma presheafAdjunction_homEquiv_apply {C : Type u} [SmallCategory C] {V : C}
    (G : (Over V)ᵒᵖ ⥤ Type u) (F : Cᵒᵖ ⥤ Type u) (α : presheaf G ⟶ F) :
    (presheafAdjunction (U := V)).homEquiv G F α = toRestricted G α := by
  simp only [presheafAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- **The bijection of `OverShriek.presheafAdjunction` composed before sheafification**: sheafify,
then restrict the resulting map out of the coproduct presheaf. -/
private lemma presheafAdjunction_comp_homEquiv_apply {C : Type u} [SmallCategory C] {V : C}
    (J : GrothendieckTopology C) (G : (Over V)ᵒᵖ ⥤ Type u) (Y : Sheaf J (Type u))
    (g : (presheafFunctor (U := V) ⋙ presheafToSheaf J (Type u)).obj G ⟶ Y) :
    ((presheafAdjunction (U := V)).comp (sheafificationAdjunction J (Type u))).homEquiv G Y g =
      toRestricted G (toSheafify J (presheaf G) ≫ g.hom) := by
  rw [Adjunction.comp_homEquiv_apply, sheafificationAdjunction_homEquiv_apply']
  exact presheafAdjunction_homEquiv_apply G _ _

/-! ### The tautological section -/

/-- **The structure map of `Φ_V H` is the tautological section.**  Under the adjunction
`j_{V!} ⊣ j_V^{-1}`, the structure map `j_{V!}H ⟶ h_V^#` of `Φ_V H` — read on `j_{V!}H` through
Stacks 03CD's `sheafFunctorToOverForgetIso` — corresponds to the map of sheaves on `C/V` sending a
section over `(X, a)` to the image `a^#` of `a` in `h_V^#(X)`.

Both `j_{V!}` and its adjunction are Mathlib's chosen ones, hence opaque; the proof pins them
against the coproduct presheaf of Stacks 00Y1, whose own adjunction `presheafAdjunction` has
`OverShriek.toRestricted` for its hom-set bijection, by the defining property of the comparison
`sheafifyNatIso` of two left adjoints of the same functor. -/
private lemma homEquiv_hom_sheafFunctorToOver {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (V : C) (H : Sheaf (J.over V) (Type u)) :
    (((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J).homEquiv H
        ((presheafToSheaf J (Type u)).obj (yoneda.obj V))
        ((sheafFunctorToOverForgetIso (U := V) J).inv.app H ≫
          ((sheafFunctorToOver (U := V) J).obj H).hom)).hom =
      toRestricted H.obj (presheafToYoneda H.obj ≫ toSheafify J (yoneda.obj V)) := by
  -- The structure map of `Φ_V H` is the sheafification of the tautological section `γ`.
  have hnat : toSheafify J (presheaf H.obj) ≫
        ((presheafToSheaf J (Type u)).map (presheafToYoneda H.obj)).hom =
      presheafToYoneda H.obj ≫ toSheafify J (yoneda.obj V) :=
    (toSheafify_naturality J (presheafToYoneda H.obj)).symm
  -- Stacks 03CD at the *presheaf* `H.obj` factors through Stacks 03CD at the *sheaf* `H`.
  have e1 : ((Over.forget V).sheafPullback (Type u) (J.over V) J).map
        ((sheafificationAdjunction (J.over V) (Type u)).counit.app H) ≫
      (sheafFunctorToOverForgetIso (U := V) J).inv.app H =
      (sheafifyNatIso (U := V) J).hom.app H.obj :=
    Iso.hom_inv_id_assoc
      (((Over.forget V).sheafPullback (Type u) (J.over V) J).mapIso
        ((asIso (sheafificationAdjunction (J.over V) (Type u)).counit).app H))
      ((sheafifyNatIso (U := V) J).hom.app H.obj)
  have hmap1 : ((Over.forget V).sheafPullback (Type u) (J.over V) J).map
          ((sheafificationAdjunction (J.over V) (Type u)).counit.app H) ≫
        ((sheafFunctorToOverForgetIso (U := V) J).inv.app H ≫
          ((sheafFunctorToOver (U := V) J).obj H).hom) =
      (sheafifyNatIso (U := V) J).hom.app H.obj ≫
        ((sheafFunctorToOver (U := V) J).obj H).hom :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun x => x ≫ ((sheafFunctorToOver (U := V) J).obj H).hom) e1)
  have hnl : (((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J).homEquiv
          ((presheafToSheaf (J.over V) (Type u)).obj H.obj)
          ((presheafToSheaf J (Type u)).obj (yoneda.obj V)))
        ((sheafifyNatIso (U := V) J).hom.app H.obj ≫
          ((sheafFunctorToOver (U := V) J).obj H).hom) =
      (sheafificationAdjunction (J.over V) (Type u)).counit.app H ≫
        (((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J).homEquiv H
          ((presheafToSheaf J (Type u)).obj (yoneda.obj V)))
          ((sheafFunctorToOverForgetIso (U := V) J).inv.app H ≫
            ((sheafFunctorToOver (U := V) J).obj H).hom) := by
    rw [← hmap1]
    exact Adjunction.homEquiv_naturality_left _ _ _
  -- `sheafifyNatIso` (Stacks 03CD) compares the two left adjoints of `j_V^{-1}` followed by the
  -- inclusion of sheaves into presheaves, so it identifies their hom-set bijections; the two
  -- bijections are then `toSheafify` and `toRestricted`.
  have hs := Adjunction.homEquiv_leftAdjointUniq_hom_app_comp
    ((sheafificationAdjunction (J.over V) (Type u)).comp
      ((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J))
    ((presheafAdjunction (U := V)).comp (sheafificationAdjunction J (Type u)))
    (x := H.obj) (((sheafFunctorToOver (U := V) J).obj H).hom)
  have key := (sheafificationAdjunction_comp_homEquiv_apply (J.over V)
        ((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J) H.obj
        ((presheafToSheaf J (Type u)).obj (yoneda.obj V))
        ((sheafifyNatIso (U := V) J).hom.app H.obj ≫
          ((sheafFunctorToOver (U := V) J).obj H).hom)).symm.trans
    (hs.trans ((presheafAdjunction_comp_homEquiv_apply J H.obj
        ((presheafToSheaf J (Type u)).obj (yoneda.obj V))
        ((sheafFunctorToOver (U := V) J).obj H).hom).trans
      (congrArg (toRestricted H.obj) hnat)))
  refine Eq.trans ?_ key
  rw [hnl]
  simp [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc, Category.id_comp]

/-! ### The identification `f⁻¹h_V^# ≅ h_U^#` of Stacks 04D3 on tautological sections -/

/-- **A map out of `h_V^#` is determined on tautological sections by its value at the identity.**
If `β : h_V^# ⟶ u_p h_U^#` carries the tautological section `𝟙_V^#` to the tautological section
`𝟙_U^#`, then it carries `a^#` to `(u a)^#` for every `a : W ⟶ V`.

Both steps are naturality of the Yoneda bijection (`CategoryTheory.map_yonedaEquiv`) for the maps
`h_V ⟶ h_V^# ⟶ u_p h_U^#` and `h_U ⟶ h_U^#`. -/
private lemma app_toSheafify_of_app_id {C : Type u} [SmallCategory C] {D : Type u}
    [SmallCategory D] (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D) (V : C)
    (β : ((presheafToSheaf J (Type u)).obj (yoneda.obj V)).obj ⟶
      u.op ⋙ ((presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V))).obj)
    (hβ : β.app (op V) ((toSheafify J (yoneda.obj V)).app (op V) (𝟙 V)) =
      (toSheafify K (yoneda.obj (u.obj V))).app (op (u.obj V)) (𝟙 (u.obj V)))
    {W : C} (a : W ⟶ V) :
    β.app (op W) ((toSheafify J (yoneda.obj V)).app (op W) a) =
      (toSheafify K (yoneda.obj (u.obj V))).app (op (u.obj W)) (u.map a) := by
  rw [← map_yonedaEquiv (toSheafify K (yoneda.obj (u.obj V))) (u.map a), yonedaEquiv_apply, ← hβ]
  exact (map_yonedaEquiv (toSheafify J (yoneda.obj V) ≫ β) a).symm

/-- **Stacks 04D3's identification `f⁻¹h_V^# ≅ h_U^#` on tautological sections.**  Transported
across `f⁻¹ ⊣ f_*`, it carries the section `a^#` of `h_V^#` over `X` to the section `(u a)^#` of
`h_U^#` over `u X`, for every `a : X ⟶ V`.

By `app_toSheafify_of_app_id` only the value at the identity is at issue, and that is the defining
corepresentability property of `sheafPullbackSheafifyYonedaIso`, which says that the section
corresponding to it is the tautological section `𝟙_U^#`. -/
private lemma homEquiv_sheafPullbackSheafifyYonedaIso_app {C : Type u} [SmallCategory C]
    {D : Type u} [SmallCategory D] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [u.IsContinuous J K] (V : C) {W : C} (a : W ⟶ V) :
    (((u.sheafAdjunctionContinuous (Type u) J K).homEquiv
            ((presheafToSheaf J (Type u)).obj (yoneda.obj V))
            ((presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V))))
          (sheafPullbackSheafifyYonedaIso u J K V).hom).hom.app (op W)
        ((toSheafify J (yoneda.obj V)).app (op W) a) =
      (toSheafify K (yoneda.obj (u.obj V))).app (op (u.obj W)) (u.map a) :=
  app_toSheafify_of_app_id J K u V _ (by
    have h := sheafPullbackSheafifyYonedaIso_hom_comp u J K V
      ((presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V))) (𝟙 _)
    rw [Category.comp_id] at h
    have hl : lhsEquiv u J K V ((presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V)))
          (sheafPullbackSheafifyYonedaIso u J K V).hom =
        yonedaEquiv ((sheafificationAdjunction J (Type u)).homEquiv _ _
          ((u.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _
            (sheafPullbackSheafifyYonedaIso u J K V).hom)) := rfl
    have hr : rhsEquiv u K V ((presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V))) (𝟙 _) =
        yonedaEquiv ((sheafificationAdjunction K (Type u)).homEquiv _ _
          (𝟙 ((presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V))))) := rfl
    rw [hl, hr, Adjunction.homEquiv_id, sheafificationAdjunction_unit_app,
      sheafificationAdjunction_homEquiv_apply', yonedaEquiv_apply, yonedaEquiv_apply] at h
    exact h) a

/-! ### The comparison of Stacks 03CF's clause (d) on hom-sets -/

/-- **The comparison `(f')⁻¹j_{U!} ≅ j_{V!}f⁻¹` of Stacks 03CF on hom-sets.**  Precomposition with
it identifies the hom-set bijection of `(f')⁻¹ ⋙ j_{U!} ⊣ j_U^{-1} ⋙ f'_*` with that of
`j_{V!} ⋙ f⁻¹ ⊣ f_* ⋙ j_V^{-1}`, the two right adjoints being equal by clause (d).

This is the whole use made of `sheafPullbackOverPostIso`; nothing else about it is needed, because
it is an `Adjunction.leftAdjointUniq`. -/
private lemma homEquiv_sheafPullbackOverPostIso {C : Type u} [SmallCategory C] {D : Type u}
    [SmallCategory D] (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
    [u.IsContinuous J K] (V : C)
    (H : Sheaf (J.over V) (Type u)) (Y : Sheaf K (Type u))
    (g : (u.sheafPullback (Type u) J K).obj
        (((Over.forget V).sheafPullback (Type u) (J.over V) J).obj H) ⟶ Y) :
    (((Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V)
          (K.over (u.obj V))).homEquiv H _)
        ((((Over.forget (u.obj V)).sheafAdjunctionContinuous (Type u) (K.over (u.obj V))
              K).homEquiv _ Y)
          ((sheafPullbackOverPostIso J K u V (Type u)).hom.app H ≫ g)) =
      (((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J).homEquiv H _)
        (((u.sheafAdjunctionContinuous (Type u) J K).homEquiv _ Y) g) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app_comp
    (((Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V)
        (K.over (u.obj V))).comp
      ((Over.forget (u.obj V)).sheafAdjunctionContinuous (Type u) (K.over (u.obj V)) K))
    ((sheafPushforwardContinuous_overPost_eq J K u V (Type u)).symm ▸
      (((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J).comp
        (u.sheafAdjunctionContinuous (Type u) J K))) (x := H) g
  rw [Adjunction.comp_homEquiv_apply] at h
  exact h.trans (Adjunction.comp_homEquiv_apply
    ((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J)
    (u.sheafAdjunctionContinuous (Type u) J K) g)

/-! ### Stacks 04IU, before the identifications of Stacks 00Y1 -/

/-- The presheaf map underlying `v^s f`, for a continuous functor `v`, is `f` restricted along
`v`. -/
private lemma sheafPushforwardContinuous_map_hom {A : Type*} [Category A] {B : Type*} [Category B]
    (v : A ⥤ B) (J : GrothendieckTopology A) (K : GrothendieckTopology B) [v.IsContinuous J K]
    {X Y : Sheaf K (Type u)} (f : X ⟶ Y) :
    ((v.sheafPushforwardContinuous (Type u) J K).map f).hom =
      Functor.whiskerLeft v.op f.hom := rfl

/-- **Stacks 04IU on the level of `j_{U!}` and `j_{V!}`.**  The comparison of Stacks 03CF's clause
(d), followed by `f⁻¹` of the structure map of `Φ_V H` and by Stacks 04D3's identification, is the
structure map of `Φ_U((f')⁻¹H)`:
```
  (f')⁻¹j_{U!}-comparison ≫ f⁻¹(j_{V!}H ⟶ h_V^#) ≫ (f⁻¹h_V^# ≅ h_U^#) = (j_{U!}(f')⁻¹H ⟶ h_U^#) .
```
Both sides are morphisms out of `j_{U!}(f')⁻¹H`, so they are compared under
`(f')⁻¹ ⋙ j_{U!} ⊣ j_U^{-1} ⋙ f'_*`, where both become the tautological section of
`j_V^{-1}f_*h_U^#`: on the left by `homEquiv_hom_sheafFunctorToOver` and
`homEquiv_sheafPullbackSheafifyYonedaIso_app`, on the right by `homEquiv_hom_sheafFunctorToOver`
again, since `Over.post u` sends `(X, a)` to `(u X, u a)`. -/
private lemma sheafPullbackOverPostIso_hom_app_comp {C : Type u} [SmallCategory C] {D : Type u}
    [SmallCategory D] (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
    [u.IsContinuous J K] (V : C)
    (H : Sheaf (J.over V) (Type u)) :
    (sheafPullbackOverPostIso J K u V (Type u)).hom.app H ≫
        ((u.sheafPullback (Type u) J K).map
            ((sheafFunctorToOverForgetIso (U := V) J).inv.app H ≫
              ((sheafFunctorToOver (U := V) J).obj H).hom) ≫
          (sheafPullbackSheafifyYonedaIso u J K V).hom) =
      (sheafFunctorToOverForgetIso (U := u.obj V) K).inv.app
          (((Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V))).obj H) ≫
        ((sheafFunctorToOver (U := u.obj V) K).obj
          (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
            (K.over (u.obj V))).obj H)).hom := by
  apply ((((Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V)
        (K.over (u.obj V))).comp
      ((Over.forget (u.obj V)).sheafAdjunctionContinuous (Type u) (K.over (u.obj V)) K)).homEquiv H
    ((presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V)))).injective
  simp only [Adjunction.comp_homEquiv_apply]
  rw [homEquiv_sheafPullbackOverPostIso, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  refine Sheaf.hom_ext ?_
  rw [Adjunction.homEquiv_apply
    ((Over.post (X := V) u).sheafAdjunctionContinuous (Type u) (J.over V) (K.over (u.obj V)))]
  simp only [ObjectProperty.FullSubcategory.comp_hom, sheafPushforwardContinuous_map_hom,
    homEquiv_hom_sheafFunctorToOver]
  ext W s
  exact homEquiv_sheafPullbackSheafifyYonedaIso_app J K u V W.unop.hom

/-- Cancelling an isomorphism on the left: an equation `p ≫ z ≫ m = i.inv ≫ k` between morphisms
out of the target of `i` gives `(i.hom ≫ p ≫ z) ≫ m = k`. -/
private lemma comp_eq_of_eq_inv_comp {A : Type*} [Category A] {W X Y Z T : A} (i : W ≅ X)
    (p : X ⟶ Y) (z : Y ⟶ Z) {m : Z ⟶ T} {k : W ⟶ T} (h : p ≫ z ≫ m = i.inv ≫ k) :
    (i.hom ≫ p ≫ z) ≫ m = k := by
  rw [Category.assoc, Category.assoc, h, Iso.hom_inv_id_assoc]

private theorem underlyingIso_hom_app_comp_hom_proof {C : Type u} [SmallCategory C] {D : Type u}
    [SmallCategory D] {J : GrothendieckTopology C} {K : GrothendieckTopology D} {u : C ⥤ D}
    [u.IsContinuous J K]
    (hu : u.IsMorphismOfSites J K) (V : C) (H : Sheaf (J.over V) (Type u)) :
    (underlyingIso J K u V).hom.app H ≫
        ((sheafFunctorToOver (U := V) J ⋙
            (hu.morphismOfTopoi.over
                ((presheafToSheaf J (Type u)).obj (yoneda.obj V))).inverseImage ⋙
            Over.map (sheafPullbackSheafifyYonedaIso u J K V).hom).obj H).hom =
      (((Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V)) ⋙
          sheafFunctorToOver (U := u.obj V) K).obj H).hom := by
  have h := sheafPullbackOverPostIso_hom_app_comp J K u V H
  simp only [Functor.map_comp, Category.assoc] at h
  exact comp_eq_of_eq_inv_comp
    ((sheafFunctorToOverForgetIso (U := u.obj V) K).app
      (((Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V))).obj H))
    ((sheafPullbackOverPostIso J K u V (Type u)).hom.app H)
    ((u.sheafPullback (Type u) J K).map ((sheafFunctorToOverForgetIso (U := V) J).inv.app H)) h

end Stacks.SliceTopos.LocalizationCompare

@[expose] public section

open Stacks.SliceTopos.LocalizationCompare in
/-- **Stacks 04IU.**  Let `u : C ⥤ D` be a continuous functor between sites defining a morphism of
sites, with induced morphism of topoi `f : Sh(D) ⟶ Sh(C)`, let `V` be an object of `C` and put
`U = u V`.  Localizing the morphism of sites at `V` (Stacks 03CF) gives
`f' : Sh(D/U) ⟶ Sh(C/V)` with `(f')⁻¹ = u'_s` for `u' = Over.post u`; localizing the morphism of
topoi at the sheaf `h_V^#` (Stacks 04H1) gives `f'' : Sh(D)/f⁻¹h_V^# ⟶ Sh(C)/h_V^#` with
`(f'')⁻¹ = Over.post f⁻¹`.  Through the equivalences `Φ_V, Φ_U` of Stacks 00Y1 and the
identification `f⁻¹h_V^# ≅ h_U^#` of Stacks 04D3 the two agree:
```
  (f')⁻¹ ⋙ Φ_U  ≅  Φ_V ⋙ (f'')⁻¹ ⋙ Over.map (04D3) .
```
Both sides become `j_{U!}(f')⁻¹ ≅ f⁻¹j_{V!}` after `Over.forget h_U^#`, canonically and for free,
by `underlyingIso`; the content of the lemma, stated here, is that that canonical isomorphism
respects the structure maps to `h_U^#`, the one on the right being computed with Stacks 04D3's
identification.  Feeding this equation to `Over.natIsoOfForgetIso` produces the displayed
isomorphism of functors, hence the agreement of the diagram of Stacks 04H1 with the diagram of
Stacks 03CF via the identifications `j_F = j_U`, `j_G = j_V` of Stacks 04IQ. -/
@[stacks 04IU]
public theorem underlyingIso_hom_app_comp_hom {C : Type u} [SmallCategory C] {D : Type u}
    [SmallCategory D] {J : GrothendieckTopology C} {K : GrothendieckTopology D} {u : C ⥤ D}
    [u.IsContinuous J K]
    (hu : u.IsMorphismOfSites J K) (V : C) (H : Sheaf (J.over V) (Type u)) :
    (underlyingIso J K u V).hom.app H ≫
        ((sheafFunctorToOver (U := V) J ⋙
            (hu.morphismOfTopoi.over
                ((presheafToSheaf J (Type u)).obj (yoneda.obj V))).inverseImage ⋙
            Over.map (sheafPullbackSheafifyYonedaIso u J K V).hom).obj H).hom =
      (((Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V)) ⋙
          sheafFunctorToOver (U := u.obj V) K).obj H).hom := by
  apply Stacks.SliceTopos.LocalizationCompare.underlyingIso_hom_app_comp_hom_proof
end

end

end CategoryTheory.SliceTopos

/-! # Relocalizing a morphism of sites at `c : U ⟶ u(V)`, and the morphism of topoi at `s`

Let `u : C ⥤ D` be a continuous functor between the sites `(C, J)` and `(D, K)` defining a morphism
of sites, so that it induces a morphism of topoi `f : Sh(D) ⟶ Sh(C)` with `f⁻¹ = u_s` (Stacks
00XC).  Let `V` be an object of `C`, let `U` be an object of `D` and let `c : U ⟶ u V`.  (Stacks
writes the morphism of sites as `f : C → D` with the continuous functor running backwards,
`u : D → C`; so Stacks' `C` is this file's `D` and vice versa, and Stacks' `V ∈ Ob(D)`,
`U ∈ Ob(C)`, `c : U → u(V)` are this file's `V : C`, `U : D`, `c : U ⟶ u V`.)

Two morphisms of topoi are attached to `c`, one for each way of localizing.

*The site-side one*, Stacks 04IN: `f_c = f' ∘ j_{U/u(V)}`, the localization `f'` of the morphism
of sites at `V` (Stacks 03CF, `(f')⁻¹ = (Over.post u)_s`) composed with the relocalization
`j_{U/u(V)}` of Stacks 03EH along `c`, whose inverse image is restriction along
`Over.map c : D/U ⥤ D/u(V)`.  So `(f_c)⁻¹ = (Over.post u)_s ⋙ (Over.map c)^s`.

*The topos-side one*, Stacks 04IV: put `G = h_V^#`, `F = h_U^#` and let
`s : F ⟶ f⁻¹G` be the morphism induced by `c`, namely `h_c^#` followed by Stacks 04D3's
identification `h_{u(V)}^# ≅ f⁻¹h_V^#`; then `f_s = f' ∘ j_{F/f⁻¹G}` is the localization of the
morphism of *topoi* (Stacks 04H1) composed with the relocalization of Stacks 04IR, and Stacks 04IV
characterises it by
```
  (f_s)⁻¹(H --φ--> G) = (f⁻¹H ×_{f⁻¹φ, f⁻¹G, s} F ⟶ F) .
```
In this repository `f_s` is `MorphismOfTopoi.relocalize` (`Sites/RelocalizationMorphism.lean`),
which is stated — as Stacks 04H1 is, and for the same reason, Remark 03CJ — for an arbitrary
morphism of topoi and arbitrary objects of the two topoi, so it covers Stacks 04IN and Stacks 04IV
at once; what is *not* covered there, and is the content of Stacks 04IW, is the passage from the
site `D/U` to the slice `Sh(D)/h_U^#`.

Stacks 04IW says the two diagrams agree via the identifications `j_F = j_U`, `j_G = j_V` of
Stacks 04IQ, i.e. via the equivalences `Φ_U : Sh(D/U) ≌ Sh(D)/h_U^#` and
`Φ_V : Sh(C/V) ≌ Sh(C)/h_V^#` of Stacks 00Y1.  Since the horizontal edges are identified by
Stacks 04IQ and both squares commute, the assertion is about the vertical edges:
```
  (f_c)⁻¹ ⋙ Φ_U  ≅  Φ_V ⋙ (f_s)⁻¹ : Sh(C/V) ⥤ Sh(D)/h_U^# ,
```
and by Stacks 04IV's characterisation of `(f_s)⁻¹` this says exactly that `Φ_U((f_c)⁻¹H)` *is* the
fibre product `f⁻¹(j_{V!}H) ×_{f⁻¹h_V^#, s} h_U^#`, with its structure map to `h_U^#`, through the
canonical comparison map.  That cartesian square is what is stated here.

## Main results

* `CategoryTheory.SliceTopos.isPullback_sheafFunctorToOver_overMap_overPost` (Stacks 04IW): for
  every sheaf `H` on `C/V` the square
  ```
    Φ_U((f_c)⁻¹H) -----> f⁻¹(j_{V!}H)
        |                     |
        |                     | f⁻¹(structure map of Φ_V H)
        v                     v
      h_U^#  ------s------> f⁻¹h_V^#
  ```
  is cartesian, its top edge being the canonical comparison map: Stacks 04IL (1) (= Stacks 04IS)
  identifies `j_{U/u(V)}⁻¹ ⋙ Φ_U` with `Φ_{u(V)} ⋙ Over.pullback h_c^#`, and Stacks 03CF's
  `underlyingIso` (= Stacks 04IU) identifies `j_{u(V)!}(f')⁻¹H` with `f⁻¹j_{V!}H`.

## Implementation notes

The conclusion is a cartesian square rather than an isomorphism of functors, for the reason that
Stacks 04IV *characterises* `(f_s)⁻¹` by the fibre-product rule: saying that the two diagrams agree
is saying that the site-side `(f_c)⁻¹`, read in `Sh(D)` through `Φ_U`, satisfies that rule, and the
isomorphism `(f_c)⁻¹ ⋙ Φ_U ≅ Φ_V ⋙ (f_s)⁻¹` in `Over h_U^#` then follows, since
`(f_s)⁻¹(Φ_V H) = (Over.pullback s).obj ((Over.post f⁻¹).obj (Φ_V H))` is by definition
(`MorphismOfTopoi.relocalize_inverseImage_obj`) the fibre product of the cospan appearing here,
with `pullback.snd` as its structure map; it is natural in `H` because every edge of the square is.
So the cospan in the statement is not an ad hoc one: it is the value of `(f_s)⁻¹`.  An existence
statement about that isomorphism would be weaker: an arbitrary isomorphism of those two functors
says nothing about which comparison map is the identification, and the identification is the whole
assertion of Stacks 04IW.  For the same reason `s` is pinned as `h_c^#` followed by the inverse of
Stacks 04D3's `sheafPullbackSheafifyYonedaIso`, not by an unspecified isomorphism
`h_{u(V)}^# ≅ f⁻¹h_V^#`.

The hypotheses are those of Stacks 03EF — `C` has finite limits and `u` is left exact — rather than
Stacks 04IW's bare "morphism of sites", exactly as for Stacks 04IU: they are the generality in
which the repository's Stacks 03CF has `Over.post u` continuous (`Functor.isContinuous_overPost`)
and in which `underlyingIso` is stated, and they are the situation the source's own proof of Stacks
04H1 works in (a continuous functor satisfying the assumptions of Proposition 00X6 between sites
with finite limits).  Unlike Stacks 04IU, `u.IsMorphismOfSites J K` is *not* taken as a hypothesis:
no `MorphismOfTopoi` occurs in the statement — only `f⁻¹ = u_s` does — and under these hypotheses
it is implied anyway by Stacks 00X6 (`Functor.isMorphismOfSites_of_preservesFiniteLimits`), so
carrying it would be a hypothesis the conclusion does not use.

The object `U` and the morphism `c` are arbitrary, as in Stacks 04IN and Stacks 04IV; Stacks 04IU
is the case `U = u V`, `c = 𝟙`, where the fibre product collapses and only the identification of
the two lower right corners is left.  The last squares of Stacks 04IN and Stacks 04IV —
compatibility with `b : V' ⟶ V`, `a : U' ⟶ U` — are `MorphismOfTopoi.relocalizeCompPullbackIso`.

Faithfulness, on the four points a reader should check against the source.  (1) No hypothesis is
dead: `V`, `U`, `c` are the data the two diagrams are built from and all three occur in the square,
`H` is the sheaf at which the vertical edges are compared, and the finite-limit hypotheses are what
make `Over.post u` continuous, hence the site-side `f'` — and with it `f_c` — exist.  (2) The sites
are the source's: `(C, J)` and `(D, K)` are given, the slices carry the localized topologies
`J.over V`, `K.over U` and `K.over (u V)` induced by them, and the sheaves are sheaves of sets.
(3) Every map is pinned, none merely asserted to exist: the identification of the horizontal edges
is Stacks 04IQ (`OverShriek.overPullbackCompSheafFunctorToOverIso` and companions), the
identification `Sh(D/U) = Sh(D)/h_U^#` is Stacks 00Y1's `OverShriek.sheafFunctorToOver`, `s` is
`h_c^#` composed with the inverse of Stacks 04D3's isomorphism, and the comparison map is the
composite of Stacks 04IL (1)'s and Stacks 03CF's own identifications, so the cartesian square
determines the isomorphism of the two diagrams rather than merely asserting one.  (4) The
instantiation is not degenerate: take `u = 𝟭 C`, `K = J`, `U = V`, `c = 𝟙 V`, where `f` is the
identity morphism of topoi, `s` is an isomorphism, and the square says that `j_{V!}H`, with its
structure map, is the fibre product of `j_{V!}H ⟶ h_V^#` along that isomorphism — a nonvacuous
cartesian square, since it pins the comparison map to be the canonical one.  A second witness,
where the fibre product is not a corner: `u = 𝟭 C`, `K = J`, `V` any object and `c : U ⟶ V` any
morphism, where the square is Stacks 04IL (1) for `c`, i.e. `j_{U/V}⁻¹` is base change along
`h_c^#`.

## References

Stacks Project, tag 04IW (`sites-lemma-relocalize-morphism-topoi-compare`); the two diagrams
compared are those of tag 04IN and tag 04IV, the identifications are tag 04IQ (`j_F = j_U`,
`j_G = j_V`) and tag 04D3 (`f⁻¹h_V^# = h_{u(V)}^#`), and the source's proof is "combine tag 04IS
with tag 04IU".

* [Stacks 04IW](https://stacks.math.columbia.edu/tag/04IW)
-/

namespace CategoryTheory.SliceTopos

section

universe u
open CategoryTheory Limits
open OverShriek
open CategoryTheory Limits CategoryTheory.SliceTopos CategoryTheory.OverShriek

namespace Stacks.SliceTopos.RelocalizationSquare

/-- **An isomorphism in `Over X` is a cartesian square over `𝟙 X`.**  The square whose horizontal
edges are `e.left` and `𝟙 X` and whose vertical edges are the two structure maps commutes by
`Over.w`, and both its horizontal edges are invertible. -/
private lemma isPullback_left_of_isIso {T : Type*} [Category T] {X : T} {A B : Over X} (e : A ⟶ B)
    [IsIso e] : IsPullback e.left A.hom B.hom (𝟙 X) := by
  have : IsIso e.left := inferInstanceAs (IsIso ((Over.forget X).map e))
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- **Stacks 04IL (1) (= Stacks 04IS), read as a cartesian square.**  For `c : U ⟶ W` in `D` and a
sheaf `G` on `D/W`, the sheaf `Φ_U((Over.map c)^s G)` over `h_U^#` *is* the base change of
`Φ_W G` over `h_W^#` along `h_c^#`:
```
    Φ_U((Over.map c)^s G) -----> Φ_W G
        |                          |
        v                          v
      h_U^# -------h_c^#-------> h_W^#
```
is cartesian.  Stacks 04IL (1) provides the isomorphism in `Over h_U^#` of the left-hand corner
with that base change, and the base change is cartesian along `h_c^#`. -/
private lemma isPullback_sheafFunctorToOver_overMap {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) {U W : D} (c : U ⟶ W) (G : Sheaf (K.over W) (Type u)) :
    IsPullback
      (((inverseImageCompSheafFunctorToOverIso c K).hom.app G).left ≫
        pullback.fst ((sheafFunctorToOver (U := W) K).obj G).hom
          ((presheafToSheaf K (Type u)).map (yoneda.map c)))
      ((sheafFunctorToOver (U := U) K).obj
        (((Over.map c).sheafPushforwardContinuous (Type u) (K.over U) (K.over W)).obj G)).hom
      ((sheafFunctorToOver (U := W) K).obj G).hom
      ((presheafToSheaf K (Type u)).map (yoneda.map c)) := by
  simpa using
    (isPullback_left_of_isIso
        ((inverseImageCompSheafFunctorToOverIso c K).hom.app G)).paste_horiz
      (IsPullback.of_hasPullback ((sheafFunctorToOver (U := W) K).obj G).hom
        ((presheafToSheaf K (Type u)).map (yoneda.map c)))

/-- **Stacks 04IU, read as a cartesian square.**  The canonical isomorphism
`j_{u(V)!}(Over.post u)_s H ≅ f⁻¹j_{V!}H` of the proof of Stacks 03CF is a cartesian square
```
    Φ_{u(V)}((Over.post u)_s H) -----> f⁻¹(j_{V!}H)
        |                                    |
        v                                    v
      h_{u(V)}^# -----(04D3)⁻¹-------> f⁻¹h_V^#
```
its horizontal edges being invertible; the content is the commutativity, which is Stacks 04IU with
Stacks 04D3's identification `f⁻¹h_V^# ≅ h_{u(V)}^#` moved to the other side. -/
@[sga "4 IV 5.10" "(A), special case"]
private lemma isPullback_underlyingIso_hom_app {C : Type u} [SmallCategory C]
    {D : Type u} [SmallCategory D] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [u.IsContinuous J K] [HasFiniteLimits C] [PreservesFiniteLimits u] (V : C)
    (H : Sheaf (J.over V) (Type u)) :
    IsPullback ((underlyingIso J K u V).hom.app H)
      ((sheafFunctorToOver (U := u.obj V) K).obj
          (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
            (K.over (u.obj V))).obj H)).hom
      ((u.sheafPullback (Type u) J K).map ((sheafFunctorToOver (U := V) J).obj H).hom)
      (sheafPullbackSheafifyYonedaIso u J K V).inv := by
  have hu : u.IsMorphismOfSites J K :=
    Functor.isMorphismOfSites_of_preservesFiniteLimits u J K
  refine IsPullback.of_horiz_isIso ⟨(Iso.eq_comp_inv _).2 ?_⟩
  rw [Category.assoc]
  exact CategoryTheory.SliceTopos.underlyingIso_hom_app_comp_hom hu V H

private theorem isPullback_sheafFunctorToOver_overMap_overPost_proof {C : Type u} [SmallCategory C]
    {D : Type u} [SmallCategory D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {u : C ⥤ D} [u.IsContinuous J K] [HasFiniteLimits C] [PreservesFiniteLimits u]
    (V : C) {U : D} (c : U ⟶ u.obj V) (H : Sheaf (J.over V) (Type u)) :
    IsPullback
      (((inverseImageCompSheafFunctorToOverIso c K).hom.app
            (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
              (K.over (u.obj V))).obj H)).left ≫
          pullback.fst
              ((sheafFunctorToOver (U := u.obj V) K).obj
                (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
                  (K.over (u.obj V))).obj H)).hom
              ((presheafToSheaf K (Type u)).map (yoneda.map c)) ≫
            (underlyingIso J K u V).hom.app H)
      (((sheafFunctorToOver (U := U) K).obj
        (((Over.map c).sheafPushforwardContinuous (Type u) (K.over U) (K.over (u.obj V))).obj
          (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
            (K.over (u.obj V))).obj H))).hom)
      ((u.sheafPullback (Type u) J K).map ((sheafFunctorToOver (U := V) J).obj H).hom)
      ((presheafToSheaf K (Type u)).map (yoneda.map c) ≫
        (sheafPullbackSheafifyYonedaIso u J K V).inv) := by
  simpa only [Category.assoc] using
    (isPullback_sheafFunctorToOver_overMap K c
        (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
          (K.over (u.obj V))).obj H)).paste_horiz
      (isPullback_underlyingIso_hom_app J K u V H)

end Stacks.SliceTopos.RelocalizationSquare

@[expose] public section

open Stacks.SliceTopos.RelocalizationSquare in
/-- **Stacks 04IW.**  Let `u : C ⥤ D` be a continuous functor between sites defining a morphism of
sites, with induced morphism of topoi `f : Sh(D) ⟶ Sh(C)`, let `V` be an object of `C`, `U` an
object of `D` and `c : U ⟶ u V`.  Localizing the morphism of sites at `c` (Stacks 04IN) gives
`f_c : Sh(D/U) ⟶ Sh(C/V)` with `(f_c)⁻¹ = (Over.post u)_s ⋙ (Over.map c)^s`; localizing the
morphism of topoi at `s : h_U^# ⟶ f⁻¹h_V^#`, the morphism induced by `c` (Stacks 04IV), gives
`f_s : Sh(D)/h_U^# ⟶ Sh(C)/h_V^#`, characterised by
`(f_s)⁻¹(H ⟶ h_V^#) = (f⁻¹H ×_{f⁻¹h_V^#, s} h_U^# ⟶ h_U^#)`.

Through the equivalences `Φ_V, Φ_U` of Stacks 00Y1 — the identifications `j_G = j_V`, `j_F = j_U`
of Stacks 04IQ — the two agree: for every sheaf `H` on `C/V` the square
```
    Φ_U((f_c)⁻¹H) ---------> f⁻¹(j_{V!}H)
        |                          |
        |                          | f⁻¹(structure map)
        v                          v
      h_U^# ---------s---------> f⁻¹h_V^#
```
is cartesian, the top edge being the canonical comparison map assembled from Stacks 04IL (1)
(Stacks 04IS), which identifies `j_{U/u(V)}⁻¹ ⋙ Φ_U` with `Φ_{u(V)} ⋙ Over.pullback h_c^#`, and
`underlyingIso` (Stacks 04IU, Stacks 03CF), which identifies `j_{u(V)!}(f')⁻¹H` with `f⁻¹j_{V!}H`.
Equivalently: `Φ_U((f_c)⁻¹H) ≅ (f_s)⁻¹(Φ_V H)` in `Sh(D)/h_U^#`, i.e. the diagram of topoi of
Stacks 04IN agrees with the diagram of topoi of Stacks 04IV. -/
@[stacks 04IW]
public theorem isPullback_sheafFunctorToOver_overMap_overPost {C : Type u} [SmallCategory C]
    {D : Type u} [SmallCategory D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {u : C ⥤ D} [u.IsContinuous J K] [HasFiniteLimits C] [PreservesFiniteLimits u]
    (V : C) {U : D} (c : U ⟶ u.obj V) (H : Sheaf (J.over V) (Type u)) :
    IsPullback
      (((inverseImageCompSheafFunctorToOverIso c K).hom.app
            (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
              (K.over (u.obj V))).obj H)).left ≫
          pullback.fst
              ((sheafFunctorToOver (U := u.obj V) K).obj
                (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
                  (K.over (u.obj V))).obj H)).hom
              ((presheafToSheaf K (Type u)).map (yoneda.map c)) ≫
            (underlyingIso J K u V).hom.app H)
      (((sheafFunctorToOver (U := U) K).obj
        (((Over.map c).sheafPushforwardContinuous (Type u) (K.over U) (K.over (u.obj V))).obj
          (((Over.post (X := V) u).sheafPullback (Type u) (J.over V)
            (K.over (u.obj V))).obj H))).hom)
      ((u.sheafPullback (Type u) J K).map ((sheafFunctorToOver (U := V) J).obj H).hom)
      ((presheafToSheaf K (Type u)).map (yoneda.map c) ≫
        (sheafPullbackSheafifyYonedaIso u J K V).inv) := by
  apply Stacks.SliceTopos.RelocalizationSquare.isPullback_sheafFunctorToOver_overMap_overPost_proof
end

end

end CategoryTheory.SliceTopos
