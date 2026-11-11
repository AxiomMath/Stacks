module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChangeSepClosedField

/-!
# Base change for pushforward of sheaves of sets along a limit of cartesian squares

Let `I` be a preordered set and let `(X_i)`, `(S_i)`, `(T_i)`, `(Y_i)` be inverse systems of
schemes over `I` fitting into an inverse system of squares

```
X_i  ←-h_i-  Y_i
|f_i         |e_i
S_i  ←-g_i-  T_i
```

Write `X = lim X_i`, `S = lim S_i`, `T = lim T_i`, `Y = lim Y_i`, with projections
`r_i : X ⟶ X_i`, `s_i : S ⟶ S_i`, `p_i : T ⟶ T_i`, `q_i : Y ⟶ Y_i`, and let `f`, `g`, `h`, `e`
be the four limit morphisms. This file carries **conclusion (1) of Stacks 0EZT**: the assertion
that `f_i^{-1}g_{i,*}ℱ_i = h_{i,*}e_i^{-1}ℱ_i` for every `i` forces `f^{-1}g_*ℱ = h_*e^{-1}ℱ`,
for sheaves of *sets* and the underived direct images. That is the clause which
`Stacks.EtaleCohomology.LimitBaseChange` states it does not carry, having proved only the
cartesianness of the limit square and conclusion (2), for the higher direct images of abelian
sheaves.

Conclusion (1) is the input that the general case of Stacks 0EZY needs and that the finite-type
case does not reach: an affine scheme over a separably closed field is a cofiltered limit of
affine schemes of finite type, and conclusion (1) reduces the general case of Stacks 0EZY to the
finite-type case, which the library has as
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed`. The levelwise input that
reduction consumes is assembled here as
`Stacks.EtaleCohomology.LimitSetBaseChange.isIso_smallEtaleSetBaseChange_level_of_isSepClosed`.

## Main definitions

* `Stacks.EtaleCohomology.setBaseChangeApp` — the base change map `f^{-1}g_*ℱ ⟶ h_*e^{-1}ℱ` of
  a commutative square, with the two composite functors evaluated at `ℱ`.
* `Stacks.EtaleCohomology.LimitSetBaseChange.projectionPushforwardComparison`,
  `Stacks.EtaleCohomology.LimitSetBaseChange.projectionPullbackComparison` — the comparisons
  `f_* s_{i,*} ≅ r_{i,*} f_{i,*}` and `f^{-1}s_i^{-1} ≅ r_i^{-1}f_i^{-1}` of sheaves of sets
  attached to the projection square `f ≫ s_i = r_i ≫ f_i`, the second also in the form
  `Stacks.EtaleCohomology.LimitSetBaseChange.projectionPullbackComparisonApp`, with the
  composites evaluated at a sheaf.
* `Stacks.EtaleCohomology.LimitSetBaseChange.sourceTerm`,
  `Stacks.EtaleCohomology.LimitSetBaseChange.targetTerm` — the terms `s_i^{-1}g_{i,*}ℱ_i` and
  `r_i^{-1}h_{i,*}e_i^{-1}ℱ_i` of the two colimit diagrams.
* `Stacks.EtaleCohomology.LimitSetBaseChange.stageComparison` — the base change map of the `i`-th
  square, pulled back to `X`, as a map `f^{-1}s_i^{-1}g_{i,*}ℱ_i ⟶ r_i^{-1}h_{i,*}e_i^{-1}ℱ_i`.

## Main results

* `Stacks.EtaleCohomology.LimitSetBaseChange.isIso_smallEtaleSetBaseChange_limit` —
  **conclusion (1) of Stacks 0EZT**: if base change for the direct images of sheaves of sets
  holds on every level, it holds on the limit.
* `Stacks.EtaleCohomology.LimitSetBaseChange.isIso_smallEtaleSetBaseChange_level_of_isSepClosed`
  — the levelwise hypothesis of that theorem, over a separably closed field, from the
  finite-type case of Stacks 0EZY.

## Implementation notes

The source's standing hypotheses — `I` directed, the transition morphisms affine, the `g_i`
quasi-compact and quasi-separated — are not hypotheses here, exactly as in
`Stacks.EtaleCohomology.LimitBaseChange`: they are what the colimit assertion of Stacks 0EYM
needs, and that assertion is not available in this repository. The two instances of it which the
source's proof cites are therefore carried as *hypotheses*, in the same shape as in
`Stacks.EtaleCohomology.LimitBaseChange.isIso_higherBaseChangeMapAb_limit`: a diagram over `I`,
isomorphisms identifying its terms with `sourceTerm` resp. `targetTerm`, and a colimit cocone
whose vertex is the direct image at the limit, together with the comparison `α` of the two
diagrams and its compatibility with the legs (the pasting of base change maps, Stacks 0E47).
What is proved from those inputs is the source's own argument: inverse image is a left adjoint,
so it carries the first presentation to a colimit presentation of `f^{-1}g_*ℱ`, and a map of
colimit cocones invertible on every term is invertible.

Once those are hypotheses, nothing of the inverse systems survives into the proof but the
schemes and the morphisms: the levels are carried as bare families `XX`, `SS`, `TT`, `YY` of
schemes with families `f`, `g`, `h`, `e` of morphisms between them, and the limit as four
schemes with the two families of projections `r_i : X ⟶ X_i` and `s_i : S ⟶ S_i`. Neither the
functoriality of the systems, nor the limit property of the cones, nor the cartesianness of the
squares is used, so none is assumed; the system of sheaves is likewise a bare family `ℱ_i`,
since its transition maps enter the colimit presentations and nowhere else. A *fixed* base, as
in Stacks 0EZY where `S = S_i = Spec k` and `s_i = id`, is then the constant family, with no
inverse system to build.

The base change map `Stacks.EtaleCohomology.smallEtaleSetBaseChange` is a natural transformation
between two *composites* of functors, so the domain of its component at `ℱ` is
`(g_* ⋙ f^{-1}).obj ℱ` rather than `f^{-1}(g_*ℱ)`. The two are definitionally equal by one
projection, but the kernel, which does not honour reducibility attributes, answers the resulting
`Functor.obj`-congruence question by unfolding inverse image into sheafification and left Kan
extension on one side, and that times out.
`Stacks.EtaleCohomology.setBaseChangeApp` therefore names the component with the composites
evaluated, bridged by `eqToHom (Functor.comp_obj ..)`, and every statement below is phrased so
that each definitional question the kernel meets is one delta step followed by syntactic
equality.

No declaration here carries Stacks 0EZY: its general case is proved by a stalkwise argument, as
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed_of_quasiCompact` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/PushforwardBaseChangeSepClosedFieldGeneral.lean`,
not through conclusion (1). Reaching it through conclusion (1), as the source does, would use the
two colimit presentations of Stacks 0EYM, which are the hypotheses of conclusion (1), and the
presentation of an affine scheme over `Spec k` as a cofiltered limit of affine schemes of finite
type over `Spec k`, together with the Zariski-locality of the assertion on `X`, which is how the
source produces the system. The levelwise input keeps the hypothesis `hlocal` of Stacks 0EZX —
bijectivity of the base change map on sections over an étale `X_i`-scheme carrying a flat
quasi-compact factorization with geometrically connected fibres — which is proved as
`Stacks.EtaleCohomology.local_baseChange_compatible`.

## References

* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0EZY](https://stacks.math.columbia.edu/tag/0EZY)
* [Stacks Project, Tag 0EZX](https://stacks.math.columbia.edu/tag/0EZX)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)

Tags covered: 0EZT (conclusion (1), from the two colimit presentations of Stacks 0EYM and the
pasting of Stacks 0E47).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

/-! ### The base change map with the composite functors evaluated -/

section EvaluatedBaseChange

/-- From invertibility of a composite whose outer factors are transports along equalities of
objects, invertibility of the middle factor. -/
private theorem isIso_of_isIso_eqToHom_comp {C : Type*} [Category* C] {W X Y Z : C} (a : W = X)
    (x : X ⟶ Y) (b : Y = Z) (hx : IsIso (eqToHom a ≫ x ≫ eqToHom b)) : IsIso x := by
  have := hx
  have h₂ : IsIso (x ≫ eqToHom b) := IsIso.of_isIso_comp_left (eqToHom a) _
  exact IsIso.of_isIso_comp_right x (eqToHom b)

variable {X Y S T : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
  (w : e ≫ g = h ≫ f) (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v)))

/-- The component at `ℱ` of the base change map `f^{-1}g_* ⟶ h_*e^{-1}` on sheaves of sets, with
the two composite functors evaluated: a map `f^{-1}(g_*ℱ) ⟶ h_*(e^{-1}ℱ)`. -/
def setBaseChangeApp :
    (smallEtaleInverseImage.{u, v} f).obj
        ((smallEtalePushforward g (Type (max (u + 1) v))).obj F) ⟶
      (smallEtalePushforward h (Type (max (u + 1) v))).obj
        ((smallEtaleInverseImage.{u, v} e).obj F) :=
  eqToHom (Functor.comp_obj (smallEtalePushforward g (Type (max (u + 1) v)))
      (smallEtaleInverseImage.{u, v} f) F).symm ≫
    (smallEtaleSetBaseChange.{u, v} e h g f w).app F ≫
      eqToHom (Functor.comp_obj (smallEtaleInverseImage.{u, v} e)
        (smallEtalePushforward h (Type (max (u + 1) v))) F)

/-- The evaluated base change map is invertible as soon as the component of the base change map
is: they differ by two transports along equalities of objects. -/
theorem isIso_setBaseChangeApp
    (hx : IsIso ((smallEtaleSetBaseChange.{u, v} e h g f w).app F)) :
    IsIso (setBaseChangeApp.{u, v} e h g f w F) := by
  have := hx
  exact inferInstanceAs (IsIso (_ ≫ _ ≫ _))

/-- Conversely, invertibility of the evaluated base change map gives invertibility of the
component of the base change map. -/
theorem isIso_of_isIso_setBaseChangeApp
    (hy : IsIso (setBaseChangeApp.{u, v} e h g f w F)) :
    IsIso ((smallEtaleSetBaseChange.{u, v} e h g f w).app F) :=
  isIso_of_isIso_eqToHom_comp _ _ _ hy

end EvaluatedBaseChange

namespace LimitSetBaseChange

variable {I : Type w} [Preorder I] {XX SS TT YY : I → Scheme.{u}}
  (f : ∀ i, XX i ⟶ SS i) (g : ∀ i, TT i ⟶ SS i) (h : ∀ i, YY i ⟶ XX i)
  (e : ∀ i, YY i ⟶ TT i)
  {X S T Y : Scheme.{u}} (r : ∀ i, X ⟶ XX i) (s : ∀ i, S ⟶ SS i)
  (fL : X ⟶ S) (gL : T ⟶ S) (hL : Y ⟶ X) (eL : Y ⟶ T)

/-! ### The comparisons attached to the projection square -/

/-- The comparison `f_* s_{i,*} ≅ r_{i,*} f_{i,*}` of the two composite direct images of sheaves
of sets of the projection square `f ≫ s_i = r_i ≫ f_i`, assembled from the composition
isomorphism for direct image along a named composite. -/
def projectionPushforwardComparison (hfL : ∀ i, fL ≫ s i = r i ≫ f i) (i : I) :
    smallEtalePushforward fL (Type (max (u + 1) v)) ⋙
        smallEtalePushforward (s i) (Type (max (u + 1) v)) ≅
      smallEtalePushforward (r i) (Type (max (u + 1) v)) ⋙
        smallEtalePushforward (f i) (Type (max (u + 1) v)) :=
  smallEtalePushforwardComp' fL (s i) (fL ≫ s i) rfl (Type (max (u + 1) v)) ≪≫
    (smallEtalePushforwardComp' (r i) (f i) (fL ≫ s i) (hfL i) (Type (max (u + 1) v))).symm

/-- The comparison `f^{-1}s_i^{-1} ≅ r_i^{-1}f_i^{-1}` of the two composite inverse images of
sheaves of sets of the projection square `f ≫ s_i = r_i ≫ f_i`: the conjugate of
`Stacks.EtaleCohomology.LimitSetBaseChange.projectionPushforwardComparison` under the
inverse-image/direct-image adjunctions. -/
def projectionPullbackComparison (hfL : ∀ i, fL ≫ s i = r i ≫ f i) (i : I) :
    smallEtaleInverseImage.{u, v} (s i) ⋙ smallEtaleInverseImage.{u, v} fL ≅
      smallEtaleInverseImage.{u, v} (f i) ⋙ smallEtaleInverseImage.{u, v} (r i) :=
  Adjunction.leftAdjointUniq
    ((smallEtaleInverseImageAdjunction.{u, v} (s i)).comp
      (smallEtaleInverseImageAdjunction.{u, v} fL))
    (Adjunction.ofNatIsoRight
      ((smallEtaleInverseImageAdjunction.{u, v} (f i)).comp
        (smallEtaleInverseImageAdjunction.{u, v} (r i)))
      (projectionPushforwardComparison.{u, v} f r s fL hfL i).symm)

/-- The comparison `f^{-1}s_i^{-1}ℳ ≅ r_i^{-1}f_i^{-1}ℳ` at a sheaf `ℳ` on `S_i`, with the
composite functors evaluated. -/
def projectionPullbackComparisonApp (hfL : ∀ i, fL ≫ s i = r i ≫ f i) (i : I)
    (M : Sheaf (smallEtaleTopology (SS i)) (Type (max (u + 1) v))) :
    (smallEtaleInverseImage.{u, v} fL).obj ((smallEtaleInverseImage.{u, v} (s i)).obj M) ≅
      (smallEtaleInverseImage.{u, v} (r i)).obj
        ((smallEtaleInverseImage.{u, v} (f i)).obj M) :=
  eqToIso (Functor.comp_obj (smallEtaleInverseImage.{u, v} (s i))
      (smallEtaleInverseImage.{u, v} fL) M).symm ≪≫
    (projectionPullbackComparison.{u, v} f r s fL hfL i).app M ≪≫
      eqToIso (Functor.comp_obj (smallEtaleInverseImage.{u, v} (f i))
        (smallEtaleInverseImage.{u, v} (r i)) M)

/-! ### The two colimit diagrams and the levelwise base change map -/

variable (F : ∀ i, Sheaf (smallEtaleTopology (TT i)) (Type (max (u + 1) v)))

/-- The term `s_i^{-1}g_{i,*}ℱ_i` on `S` of the colimit diagram of Stacks 0EYM for `g`. -/
abbrev sourceTerm (i : I) : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v)) :=
  (smallEtaleInverseImage.{u, v} (s i)).obj
    ((smallEtalePushforward (g i) (Type (max (u + 1) v))).obj (F i))

/-- The term `r_i^{-1}h_{i,*}e_i^{-1}ℱ_i` on `X` of the colimit diagram of Stacks 0EYM for `h`
and the family of inverse images `e_i^{-1}ℱ_i`. -/
abbrev targetTerm (i : I) : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)) :=
  (smallEtaleInverseImage.{u, v} (r i)).obj
    ((smallEtalePushforward (h i) (Type (max (u + 1) v))).obj
      ((smallEtaleInverseImage.{u, v} (e i)).obj (F i)))

/-- **The levelwise comparison of the two colimit diagrams**: the base change map of the `i`-th
square on direct images of sheaves of sets, pulled back to `X` along the projection `r_i` and
read on the source through the comparison
`Stacks.EtaleCohomology.LimitSetBaseChange.projectionPullbackComparisonApp`. -/
def stageComparison (w : ∀ i, h i ≫ f i = e i ≫ g i)
    (hfL : ∀ i, fL ≫ s i = r i ≫ f i) (i : I) :
    (smallEtaleInverseImage.{u, v} fL).obj (sourceTerm.{u, v} g s F i) ⟶
      targetTerm.{u, v} h e r F i :=
  (projectionPullbackComparisonApp.{u, v} f r s fL hfL i
      ((smallEtalePushforward (g i) (Type (max (u + 1) v))).obj (F i))).hom ≫
    (smallEtaleInverseImage.{u, v} (r i)).map
      (setBaseChangeApp.{u, v} (e i) (h i) (g i) (f i) (w i).symm (F i))

omit [Preorder I] in
/-- The levelwise comparison is invertible as soon as the base change map of the `i`-th square
is: the other factor is an isomorphism. -/
theorem isIso_stageComparison (w : ∀ i, h i ≫ f i = e i ≫ g i)
    (hfL : ∀ i, fL ≫ s i = r i ≫ f i) (i : I)
    (hi : IsIso ((smallEtaleSetBaseChange.{u, v} (e i) (h i) (g i) (f i)
      (w i).symm).app (F i))) :
    IsIso (stageComparison.{u, v} f g h e r s fL F w hfL i) := by
  have h₂ : IsIso (setBaseChangeApp.{u, v} (e i) (h i) (g i) (f i) (w i).symm (F i)) :=
    isIso_setBaseChangeApp.{u, v} (e i) (h i) (g i) (f i) (w i).symm (F i) hi
  exact inferInstanceAs (IsIso (_ ≫ _))

/-! ### Conclusion (1) of Stacks 0EZT -/

/-- **Conclusion (1) of Stacks 0EZT.** Let `(ℱ_i)` be a family of sheaves of sets on the `T_i`
and let `ℱ` on `T` be a sheaf whose direct images along the limit are presented, as in Stacks
0EYM, as the colimits of the `s_i^{-1}g_{i,*}ℱ_i` and of the `r_i^{-1}h_{i,*}e_i^{-1}ℱ_i`,
compatibly with the levelwise base change maps. If the base change map of every level is an
isomorphism, so is the base change map of the limit square. -/
@[stacks 0EZT "conclusion (1): base change for the direct images of sheaves of sets passes to
the limit. The two colimit presentations `g_*ℱ = colim_i s_i^{-1}g_{i,*}ℱ_i` and
`h_*e^{-1}ℱ = colim_i r_i^{-1}h_{i,*}e_i^{-1}ℱ_i` are the two instances of Stacks 0EYM that the
source's proof cites; this repository does not prove Stacks 0EYM --
`Stacks.EtaleCohomology.LimitHigherDirectImage` constructs only its comparison maps and says so
in its own clause strings -- and the compatibility of the two with the legs is the pasting of
base change maps of Stacks 0E47. All three are carried as declared hypotheses
(`Kg`/`ρg`/`κg`/`hκg`, `Kh`/`ρh`/`κh`/`hκh`, `α`/`hα`/`hκ`), exactly as for conclusion (2) in
`Stacks.EtaleCohomology.LimitBaseChange.isIso_higherBaseChangeMapAb_limit`. What is proved is
the source's own argument from those inputs: inverse image is a left adjoint, so it carries the
first presentation to a colimit presentation of `f^{-1}g_*ℱ`, and a map of colimit cocones that
is invertible on every term is invertible. Since the two presentations are hypotheses, the
proof uses nothing of the inverse systems but the schemes and the morphisms, and the levels are
accordingly carried as bare families rather than as functors out of `Iᵒᵖ`: no functoriality, no
limit property of the cones and no cartesianness of the squares is assumed."]
theorem isIso_smallEtaleSetBaseChange_limit (w : ∀ i, h i ≫ f i = e i ≫ g i)
    (wL : hL ≫ fL = eL ≫ gL) (hfL : ∀ i, fL ≫ s i = r i ≫ f i)
    (𝓕 : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v)))
    (Kg : I ⥤ Sheaf (smallEtaleTopology S) (Type (max (u + 1) v)))
    (ρg : ∀ i, Kg.obj i ≅ sourceTerm.{u, v} g s F i)
    (κg : Kg ⟶ (Functor.const I).obj
      ((smallEtalePushforward gL (Type (max (u + 1) v))).obj 𝓕))
    (hκg : IsColimit (Cocone.mk
      ((smallEtalePushforward gL (Type (max (u + 1) v))).obj 𝓕) κg))
    (Kh : I ⥤ Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)))
    (ρh : ∀ i, Kh.obj i ≅ targetTerm.{u, v} h e r F i)
    (κh : Kh ⟶ (Functor.const I).obj
      ((smallEtalePushforward hL (Type (max (u + 1) v))).obj
        ((smallEtaleInverseImage.{u, v} eL).obj 𝓕)))
    (hκh : IsColimit (Cocone.mk
      ((smallEtalePushforward hL (Type (max (u + 1) v))).obj
        ((smallEtaleInverseImage.{u, v} eL).obj 𝓕)) κh))
    (α : Kg ⋙ smallEtaleInverseImage.{u, v} fL ⟶ Kh)
    (hα : ∀ i, (smallEtaleInverseImage.{u, v} fL).map (ρg i).hom ≫
      stageComparison.{u, v} f g h e r s fL F w hfL i = α.app i ≫ (ρh i).hom)
    (hκ : ∀ i, (smallEtaleInverseImage.{u, v} fL).map (κg.app i) ≫
      setBaseChangeApp.{u, v} eL hL gL fL wL.symm 𝓕 = α.app i ≫ κh.app i)
    (hstage : ∀ i, IsIso ((smallEtaleSetBaseChange.{u, v} (e i) (h i) (g i) (f i)
      (w i).symm).app (F i))) :
    IsIso ((smallEtaleSetBaseChange.{u, v} eL hL gL fL wL.symm).app 𝓕) := by
  have := (smallEtaleInverseImageAdjunction.{u, v} fL).leftAdjoint_preservesColimits
  refine isIso_of_isIso_setBaseChangeApp.{u, v} eL hL gL fL wL.symm 𝓕
    (LimitBaseChange.isIso_of_isColimit
      (isColimitOfPreserves (smallEtaleInverseImage.{u, v} fL) hκg) hκh α (fun i => ?_) _
      fun i => hκ i)
  have h₁ : IsIso (stageComparison.{u, v} f g h e r s fL F w hfL i) :=
    isIso_stageComparison.{u, v} f g h e r s fL F w hfL i (hstage i)
  have h₂ : IsIso (α.app i ≫ (ρh i).hom) := by rw [← hα i]; infer_instance
  exact IsIso.of_isIso_comp_right (α.app i) (ρh i).hom

/-! ### The levelwise input over a separably closed field -/

/-- The levelwise hypothesis `hstage` of
`Stacks.EtaleCohomology.LimitSetBaseChange.isIso_smallEtaleSetBaseChange_limit`, over a
separably closed field: every level of the system, being locally of finite type over `Spec k`,
satisfies base change for sheaves of sets by the finite-type case of Stacks 0EZY. The
bijectivity on sections over an étale `X_i`-scheme carrying a flat quasi-compact factorization
with geometrically connected fibres is the declared hypothesis `hlocal` of Stacks 0EZX and is
carried through, one instance per level. -/
theorem isIso_smallEtaleSetBaseChange_level_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k]
    {I : Type w} {XX TT YY : I → Scheme.{u}}
    (f : ∀ i, XX i ⟶ Spec (.of k)) (g : ∀ i, TT i ⟶ Spec (.of k))
    (h : ∀ i, YY i ⟶ XX i) (e : ∀ i, YY i ⟶ TT i)
    (hft : ∀ i, LocallyOfFiniteType (f i))
    (hsq : ∀ i, IsPullback (h i) (e i) (f i) (g i))
    (F : ∀ i, Sheaf (smallEtaleTopology (TT i)) (Type (max (u + 1) v)))
    (hlocal : ∀ (i : I) ⦃U : (XX i).Etale⦄, HasFlatConnectedFactorization (f i) U →
      Function.Bijective
        (((smallEtaleSetBaseChange.{u, v} (e i) (h i) (g i) (f i)
          (hsq i).w.symm).app (F i)).hom.app (op U)))
    (i : I) :
    IsIso ((smallEtaleSetBaseChange.{u, v} (e i) (h i) (g i) (f i)
      (hsq i).w.symm).app (F i)) := by
  let := hft i
  exact isIso_smallEtaleSetBaseChange_of_isSepClosed.{u, v} k (f i) (h i) (e i) (g i)
    (hsq i) (F i) (hlocal i)

end LimitSetBaseChange

end Stacks.EtaleCohomology

end
