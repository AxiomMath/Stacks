module

public import StacksFrontier.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import StacksFrontier.CategoryTheory.Sites.SlicePost.Pushforward
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 03CF clause (a): the localized functor is a morphism of sites

Let `u : C ⥤ D` be a functor between sites `(C, J)` and `(D, K)` defining a morphism of sites
`f : D → C`, let `V : C` and put `U = u.obj V`.  Stacks 03CF asserts, as its first clause, that
the localized functor `u' = Over.post u : Over V ⥤ Over U` again defines a morphism of sites
`f' : D/U → C/V`.  This file proves that clause **in the generality of Stacks 03CF**, i.e. from
nothing but `u.IsMorphismOfSites J K`.

Until now the repository had clause (a) only under the much stronger hypotheses of Stacks 03EF
(`Functor.isMorphismOfSites_overPost`: `C` and `D` have all finite limits and `u` is left exact),
because every criterion available for the exactness of `u'_s` routed through representable
flatness of `u'`, and because the continuity of `u'` was obtained from flatness as well.  Neither
detour is needed; both halves are proved here directly, and the route is Stacks' own, namely the
identification `Sh(C/U) ≌ Sh(C)/h_U^#` of Stacks 00Y1.

## Continuity of `u'`

`CategoryTheory.Functor.isContinuous_overPost_of_isContinuous`.  Mathlib's `Functor.IsContinuous`
is the semantic condition "`u'^p` carries sheaves to sheaves", and that is exactly what Stacks
00Y1 makes computable.  Every sheaf `G` on `D/U` is the *fibre sheaf* of its own lower shriek:
writing `(F, φ : F ⟶ h_U^#)` for `j_{U!}G` with its structure map, `G` is the sheaf
`(Y, b) ↦ {t ∈ F(Y) | φ(t) = b^#}`, which is `CategoryTheory.OverShriek.fiber` and whose
sheaf property is `CategoryTheory.OverShriek.isSheaf_fiber`, stated there for an *arbitrary*
topology on the slice.  Restricting such a fibre sheaf along `Over.post u` gives, on the nose, the
fibre presheaf cut out on `C/V` by the restrictions `u^p F ⟶ u^p h_U^#` and the tautological
section `h_V ⟶ u^p h_U^#`, `a ↦ (u a)^#`: this is `OverShriek.fiber_overPost`, a `rfl`.  Both
restrictions are sheaves because `u` is continuous, so `isSheaf_fiber` applies.

This is where the previous obstruction was: `CompatiblePreserving` for `Over.post u` asks that a
`W` over `U` mapping into `u'Y₁` and `u'Y₂` be liftable to an object of `C/V`, which bare
continuity does not provide; the module docstring of
`StacksFrontier/CategoryTheory/Sites/SlicePost/Continuous.lean` records that, and concluded that bare
continuity was "not known to suffice".  The conclusion does not follow: `CompatiblePreserving` is
only one sufficient condition for `IsContinuous`, and the fibre description bypasses it.

## Exactness of `u'_s`

Since `u'_s` is a left adjoint it is right exact, so by
`Functor.isMorphismOfSites_iff_preservesFiniteLimits` clause (a) is left exactness of `u'_s`, and
that splits into preservation of the terminal object and of fibre products.

* **Fibre products.** Taking left adjoints in clause (d) of 03CF gives
  `CategoryTheory.sheafPullbackOverPostIso`, `u'_s ⋙ j_{U!} ≅ j_{V!} ⋙ u_s`.  By Stacks 00Y1 each
  `j_{U!}` is the equivalence `Sh(C/U) ≌ Sh(C)/h_U^#` followed by `Over.forget`
  (`OverShriek.sheafFunctorToOverForgetIso`), and `Over.forget` *creates* connected limits; so
  `j_{V!}` preserves fibre products, `j_{U!}` reflects them, and `u_s` preserves finite limits by
  hypothesis.  This is `OverShriek.preservesLimitsOfShape_sheafPullback_overForget` and
  `OverShriek.reflectsLimitsOfShape_sheafPullback_overForget`.

* **Terminal object.** This is where `Over.post u` is better behaved than a general functor: the
  terminal object of `Over V` is `𝟙_V`, and `u'` sends it to `𝟙_U`, which is terminal in
  `Over U`.  A functor `F` carrying some terminal object to a terminal object has, for every `W`,
  a *terminal* object in `StructuredArrow W F` (`CategoryTheory.StructuredArrow.isTerminalMk`), so
  every `CostructuredArrow F.op Y` is connected, and the pointwise colimit formula for the left
  Kan extension `F^p = F.op.lan` then makes `F^p` of the terminal presheaf a presheaf of
  singletons.  Sheafification is left exact and `sheafToPresheaf` preserves limits, so `u'_s`
  preserves the terminal object.  Note that this argument needs no hypothesis on the topologies at
  all, and in particular does not need `u'` to be flat; flatness is what the *fibre product* half
  of the usual criterion needs.

## Main results

* `CategoryTheory.Functor.isContinuous_overPost_of_isContinuous`: `Over.post u` is continuous as
  soon as `u` is.
* `CategoryTheory.Functor.preservesTerminal_sheafPullback_of_isTerminal`: a continuous functor
  preserving some terminal object has `u_s` preserving the terminal sheaf.
* `CategoryTheory.Functor.isMorphismOfSites_overPost_of_isMorphismOfSites`: **Stacks 03CF clause
  (a)**, in the generality of 03CF.

## References

* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
-/

@[expose] public section

open CategoryTheory Opposite Limits

namespace CategoryTheory

universe u

/-! ### Continuity of `Over.post u` -/

namespace OverShriek

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]

/-- The tautological section of `u^p A` over `h_V` induced by one of `A` over `h_{u V}`: it sends
`a : X ⟶ V` to the image of `u a : u X ⟶ u V` under `ρ`. -/
def postSection (u : C ⥤ D) (V : C) {A : Dᵒᵖ ⥤ Type u} (ρ : yoneda.obj (u.obj V) ⟶ A) :
    yoneda.obj V ⟶ u.op ⋙ A where
  app X := ↾fun a => ρ.app (op (u.obj X.unop)) (u.map a)
  naturality X Y g := by
    ext a
    simpa [u.map_comp] using NatTrans.naturality_apply ρ (u.map g.unop).op (u.map a)

/-- Restricting a fibre presheaf along `Over.post u` gives the fibre presheaf of the restrictions:
both send `(X, a)` to the set of `s ∈ F(u X)` with `φ(s) = ρ(u a)`. -/
theorem fiber_overPost (u : C ⥤ D) (V : C) {A : Dᵒᵖ ⥤ Type u}
    (ρ : yoneda.obj (u.obj V) ⟶ A) {F : Dᵒᵖ ⥤ Type u} (φ : F ⟶ A) :
    (Over.post (X := V) u).op ⋙ fiber ρ φ =
      fiber (postSection u V ρ) (Functor.whiskerLeft u.op φ) := rfl

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- The restriction along `Over.post u` of a fibre presheaf of two `K`-sheaves is a
`J.over V`-sheaf, by `isSheaf_fiber` applied on `C/V` to the restrictions along `u`. -/
theorem isSheaf_fiber_overPost (u : C ⥤ D) [u.IsContinuous J K] (V : C)
    {A : Dᵒᵖ ⥤ Type u} (hA : Presheaf.IsSheaf K A) (ρ : yoneda.obj (u.obj V) ⟶ A)
    {F : Dᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf K F) (φ : F ⟶ A) :
    Presieve.IsSheaf (J.over V) ((Over.post (X := V) u).op ⋙ fiber ρ φ) := by
  have h : ∀ {B : Dᵒᵖ ⥤ Type u}, Presheaf.IsSheaf K B →
      Presheaf.IsSheaf (J.over V) ((Over.forget V).op ⋙ u.op ⋙ B) := fun hB =>
    (Over.forget V).op_comp_isSheaf (J.over V) J ⟨_, u.op_comp_isSheaf J K ⟨_, hB⟩⟩
  rw [fiber_overPost]
  exact isSheaf_fiber _ _ ((isSheaf_iff_isSheaf_of_type _ _).1 (h hF))
    ((isSheaf_iff_isSheaf_of_type _ _).1 (h hA)).isSeparated

end OverShriek

/-- **Stacks 03CF, continuity of `u'`, in the generality of 03CF.** If `u : C ⥤ D` is continuous
then so is the localized functor `Over.post u : Over V ⥤ Over (u.obj V)`.

By Stacks 00Y1 every sheaf on `D/U` is the fibre sheaf of a `K`-sheaf over `h_U^#`
(`OverShriek.sheafUnit`), and the restriction of such a fibre sheaf along `Over.post u` is the
fibre presheaf cut out on `C/V` by the restrictions along `u`, which is a sheaf by
`OverShriek.isSheaf_fiber_overPost`. -/
@[stacks 03CF "Clause (a), continuity half: `u' = Over.post u` is continuous whenever `u` is, with
  no finite-limit or flatness hypothesis. This supersedes the flatness-based
  `Functor.isContinuous_overPost_of_flat`."]
theorem Functor.isContinuous_overPost_of_isContinuous {C : Type u} [SmallCategory C] {D : Type u}
    [SmallCategory D] (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
    [u.IsContinuous J K] (V : C) :
    (Over.post (X := V) u).IsContinuous (J.over V) (K.over (u.obj V)) where
  op_comp_isSheaf_of_types G := by
    have e : G.obj ≅ OverShriek.fiber (toSheafify K (yoneda.obj (u.obj V)))
        (sheafifyMap K (OverShriek.presheafToYoneda G.obj)) :=
      (sheafToPresheaf _ _).mapIso (asIso ((OverShriek.sheafUnit K (U := u.obj V)).app G))
    exact Presieve.isSheaf_iso (J.over V)
      (Functor.isoWhiskerLeft (Over.post (X := V) u).op e).symm
      (OverShriek.isSheaf_fiber_overPost J K u V
        ((presheafToSheaf K (Type u)).obj (yoneda.obj (u.obj V))).property _
        ((presheafToSheaf K (Type u)).obj (OverShriek.presheaf G.obj)).property _)

/-! ### Exactness: the terminal object -/

section Terminal

variable {A B : Type u} [SmallCategory A] [SmallCategory B]

/-- If `F` carries a terminal object `X` of `A` to a terminal object of `B`, then for every
`W : B` the structured-arrow category `StructuredArrow W F` has a terminal object, namely the
unique arrow `W ⟶ F X`. -/
def StructuredArrow.isTerminalMk (F : A ⥤ B) {X : A} (hX : IsTerminal X)
    (hFX : IsTerminal (F.obj X)) (W : B) :
    IsTerminal (StructuredArrow.mk (hFX.from W) : StructuredArrow W F) :=
  IsTerminal.ofUniqueHom
    (fun Z => StructuredArrow.homMk (hX.from Z.right) (hFX.hom_ext _ _))
    (fun _ _ => StructuredArrow.hom_ext _ _ (hX.hom_ext _ _))

/-- A functor carrying a terminal object to a terminal object has connected costructured-arrow
categories over the opposite functor: `StructuredArrow W F` has a terminal object, hence is
connected, and `CostructuredArrow F.op (op W)` is its opposite. -/
theorem isConnected_costructuredArrow_op_of_isTerminal (F : A ⥤ B) {X : A} (hX : IsTerminal X)
    (hFX : IsTerminal (F.obj X)) (Y : Bᵒᵖ) : IsConnected (CostructuredArrow F.op Y) := by
  have : IsConnected (StructuredArrow Y.unop F) :=
    have : Nonempty (StructuredArrow Y.unop F) := ⟨StructuredArrow.mk (hFX.from Y.unop)⟩
    zigzag_isConnected fun j₁ j₂ =>
      Zigzag.trans (Zigzag.of_hom ((StructuredArrow.isTerminalMk F hX hFX Y.unop).from j₁))
        (Zigzag.of_inv ((StructuredArrow.isTerminalMk F hX hFX Y.unop).from j₂))
  exact isConnected_of_equivalent (structuredArrowOpEquivalence F Y.unop)

/-- The presheaf pullback `F^p = F.op.lan` of the terminal presheaf is terminal as soon as all the
categories `CostructuredArrow F.op Y` are connected: the pointwise formula for the left Kan
extension computes its value at `Y` as a colimit of the constant singleton diagram over
`CostructuredArrow F.op Y`. -/
noncomputable def Functor.isTerminal_lan_obj_constPUnit (F : A ⥤ B)
    (hc : ∀ Y : Bᵒᵖ, IsConnected (CostructuredArrow F.op Y)) :
    IsTerminal (F.op.lan.obj ((Functor.const Aᵒᵖ).obj (PUnit.{u + 1} : Type u))) := by
  have hobj : ∀ Y : Bᵒᵖ,
      IsTerminal ((F.op.lan.obj ((Functor.const Aᵒᵖ).obj (PUnit.{u + 1} : Type u))).obj Y) := by
    intro Y
    haveI := hc Y
    let G : CostructuredArrow F.op Y ⥤ Type u :=
      CostructuredArrow.proj F.op Y ⋙ (Functor.const Aᵒᵖ).obj (PUnit.{u + 1} : Type u)
    have e₂ : (F.op.lan.obj ((Functor.const Aᵒᵖ).obj (PUnit.{u + 1} : Type u))).obj Y ≅
        colimit G := (lanEvaluationIsoColim (Type u) F.op Y).app _
    exact IsTerminal.ofIso Types.isTerminalPUnit (e₂.trans
      ((colimit.isColimit G).coconePointUniqueUpToIso
        (isColimitConstCocone (CostructuredArrow F.op Y) (PUnit.{u + 1} : Type u)))).symm
  exact IsTerminal.ofUniqueHom
    (fun _ => { app := fun Y => (hobj Y).from _
                naturality := fun _ _ _ => (hobj _).hom_ext _ _ })
    (fun _ _ => NatTrans.ext (funext fun Y => (hobj Y).hom_ext _ _))

/-- A functor carrying some terminal object to a terminal object has left exact presheaf pullback
on terminal objects: `F^p` preserves the terminal presheaf. -/
theorem Functor.preservesTerminal_lan_of_isTerminal (F : A ⥤ B) {X : A} (hX : IsTerminal X)
    (hFX : IsTerminal (F.obj X)) :
    PreservesLimitsOfShape (Discrete PEmpty.{1})
      (F.op.lan : (Aᵒᵖ ⥤ Type u) ⥤ (Bᵒᵖ ⥤ Type u)) :=
  Functor.preservesLimitsOfShape_pempty_of_isTerminal _ Presheaf.isTerminalConstPUnit
    (Functor.isTerminal_lan_obj_constPUnit F
      (isConnected_costructuredArrow_op_of_isTerminal F hX hFX))

/-- **The terminal-object half of exactness, with no hypothesis on the topologies.** If a
continuous functor `F` carries some terminal object of `A` to a terminal object of `B`, then the
induced `F_s` on sheaves of sets preserves the terminal sheaf.

`F_s` is the composite of `sheafToPresheaf`, the presheaf pullback `F^p` and sheafification
(`Functor.sheafPullbackConstruction.sheafPullbackIso`); the outer two preserve the terminal object
because they are respectively a right adjoint and a left exact left adjoint, and the middle one
does by `Functor.preservesTerminal_lan_of_isTerminal`. -/
theorem Functor.preservesTerminal_sheafPullback_of_isTerminal (F : A ⥤ B)
    (J : GrothendieckTopology A) (K : GrothendieckTopology B) [F.IsContinuous J K]
    {X : A} (hX : IsTerminal X) (hFX : IsTerminal (F.obj X)) :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (F.sheafPullback (Type u) J K) := by
  have h₁ := Functor.preservesTerminal_lan_of_isTerminal (A := A) (B := B) F hX hFX
  have h₂ : PreservesLimitsOfShape (Discrete PEmpty.{1})
      (F.op.lan ⋙ presheafToSheaf K (Type u)) :=
    @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _ h₁ inferInstance
  have h₃ : PreservesLimitsOfShape (Discrete PEmpty.{1})
      (Functor.sheafPullbackConstruction.sheafPullback F (Type u) J K) :=
    @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _ inferInstance h₂
  exact preservesLimitsOfShape_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso F (Type u) J K).symm

end Terminal

/-! ### Exactness: fibre products -/

namespace OverShriek

universe w w'

variable {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)

/-- `j_{U!}` preserves connected limits: by Stacks 00Y1 it is an equivalence onto `Sh(D)/h_U^#`
followed by `Over.forget`, and `Over.forget` preserves connected limits. -/
@[sga "4 IV 5.3" "special case"]
theorem preservesLimitsOfShape_sheafPullback_overForget (U : D) (T : Type w) [Category.{w'} T]
    [IsConnected T] :
    PreservesLimitsOfShape T ((Over.forget U).sheafPullback (Type u) (K.over U) K) := by
  have : PreservesLimitsOfShape T
      (sheafFunctorToOver (U := U) K ⋙ Over.forget _) := inferInstance
  exact preservesLimitsOfShape_of_natIso (sheafFunctorToOverForgetIso (U := U) K)

/-- `j_{U!}` reflects connected limits, for the same reason: `Over.forget` creates them. -/
theorem reflectsLimitsOfShape_sheafPullback_overForget (U : D) (T : Type w) [Category.{w'} T]
    [IsConnected T] :
    ReflectsLimitsOfShape T ((Over.forget U).sheafPullback (Type u) (K.over U) K) := by
  have : ReflectsLimitsOfShape T
      (sheafFunctorToOver (U := U) K ⋙ Over.forget _) := inferInstance
  exact reflectsLimitsOfShape_of_natIso (sheafFunctorToOverForgetIso (U := U) K)

end OverShriek

/-- **Stacks 03CF, clause (a), in the generality of 03CF.** If `u : C ⥤ D` defines a morphism of
sites `f : D → C` and `V : C`, then the localized functor `u' = Over.post u : Over V ⥤ Over (u V)`
defines a morphism of sites `f' : D/u(V) → C/V`.

Continuity is `Functor.isContinuous_overPost_of_isContinuous`.  Exactness of `u'_s` is checked on
the terminal object and on fibre products: the former by
`Functor.preservesTerminal_sheafPullback_of_isTerminal`, since `Over.post u` carries `𝟙_V` to
`𝟙_{u V}`; the latter by `sheafPullbackOverPostIso`, `u'_s ⋙ j_{U!} ≅ j_{V!} ⋙ u_s`, together
with the fact that `j_{V!}` preserves and `j_{U!}` reflects connected limits (Stacks 00Y1) and
that `u_s` is left exact by hypothesis. -/
@[stacks 03CF "Clause (a): the localized functor `u' = Over.post u` defines a morphism of sites
  `D/u(V) → C/V`, assuming only that `u` does. This is the clause Stacks derives from clause (c)
  via 00Y1, and which `Functor.isMorphismOfSites_overPost` covers only under 03EF's finite-limit
  and left-exactness hypotheses."]
theorem Functor.isMorphismOfSites_overPost_of_isMorphismOfSites {C : Type u} [SmallCategory C]
    {D : Type u} [SmallCategory D] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) (V : C) (h : u.IsMorphismOfSites J K) :
    (Over.post (X := V) u).IsMorphismOfSites (J.over V) (K.over (u.obj V)) := by
  have := h.isContinuous
  have := h.preservesFiniteLimits
  have := Functor.isContinuous_overPost_of_isContinuous J K u V
  rw [Functor.isMorphismOfSites_iff_preservesFiniteLimits]
  -- `Over.post u` carries the terminal object `𝟙_V` of `Over V` to `𝟙_U`, so `u'_s` preserves
  -- the terminal sheaf.
  have hterm : IsTerminal ((Over.post (X := V) u).obj (Over.mk (𝟙 V))) := by
    rw [show (Over.post (X := V) u).obj (Over.mk (𝟙 V)) = Over.mk (𝟙 (u.obj V)) by simp]
    exact Over.mkIdTerminal
  have := Functor.preservesTerminal_sheafPullback_of_isTerminal (Over.post (X := V) u)
    (J.over V) (K.over (u.obj V)) Over.mkIdTerminal hterm
  -- `u'_s ⋙ j_{U!} ≅ j_{V!} ⋙ u_s` preserves fibre products, and `j_{U!}` reflects them.
  have := OverShriek.preservesLimitsOfShape_sheafPullback_overForget J V WalkingCospan
  have := OverShriek.reflectsLimitsOfShape_sheafPullback_overForget K (u.obj V) WalkingCospan
  have : PreservesLimitsOfShape WalkingCospan
      ((Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V)) ⋙
        (Over.forget (u.obj V)).sheafPullback (Type u) (K.over (u.obj V)) K) :=
    preservesLimitsOfShape_of_natIso (sheafPullbackOverPostIso J K u V (Type u)).symm
  have : PreservesLimitsOfShape WalkingCospan
      ((Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V))) :=
    preservesLimitsOfShape_of_reflects_of_preserves _
      ((Over.forget (u.obj V)).sheafPullback (Type u) (K.over (u.obj V)) K)
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

end CategoryTheory

end
