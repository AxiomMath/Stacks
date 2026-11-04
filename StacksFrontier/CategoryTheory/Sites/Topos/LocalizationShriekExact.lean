module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationOfTopoi
import StacksCore.Tactic.StacksAttribute

/-! # Exactness of extension by zero on the site of elements of a presheaf of sets

Let `(C, J)` be a site and let `K` be a presheaf of sets on `C`. The category
`C/K = CostructuredArrow yoneda K` has as objects the pairs `(U, s)` with `s ∈ K(U)`, and its
projection to `C` is `j = CostructuredArrow.proj yoneda K`. When `j` is continuous for the
restricted topology, restriction of abelian sheaves along `j` is
`j.sheafPushforwardContinuous`, the inverse image `j⁻¹` of the localization morphism of topoi
(Stacks 0791 for a sheaf `K`), and its left adjoint is extension by zero `j_!`.

This file proves that `j_!` is exact and hence that `j⁻¹` preserves injective abelian sheaves,
which is part (1) of Stacks 03F3 in the generality of a presheaf of sets in place of an object
of the site — the form Stacks 07A0 needs.

The argument is the one of the source, made structural. The functor `j_!` is the left Kan
extension along `j.op` followed by sheafification, so, sheafification being exact, exactness of
`j_!` is exactness of the Kan extension. The value of that Kan extension at `U` is the colimit
over the comma category `CostructuredArrow j.op U`, and that comma category decomposes into
connected components indexed by `K(U)`: the component of a pair `((V, s), f : U ⟶ V)` is the
one of `(U, f^*s)`, which has an initial object. So the discrete category on `K(U)` is final in
it, and the colimit is the coproduct `⨁_{t ∈ K(U)}` of the values at `(U, t)`. Coproducts of
abelian groups are exact (Grothendieck's axiom AB4), and exactness transports along a final
functor, so the colimit functor is left exact.

## Main results

* `Stacks.Sites.LocalizationShriek.lanCompEvaluationIsoColim`: for any functor, the evaluation of
  a left Kan extension is the colimit over the comma category of costructured arrows, naturally
  in the functor being extended. This is Mathlib's `CategoryTheory.lanEvaluationIsoColim` with no
  smallness hypothesis on the two categories.
* `Stacks.Sites.LocalizationShriek.Fiber.final`: the discrete category on `K(U)` is final in
  `CostructuredArrow j.op U`.
* `Stacks.Sites.LocalizationShriek.hasExactColimitsOfShape_costructuredArrow`: colimits of that
  shape in abelian groups are exact.
* `Stacks.Sites.LocalizationShriek.preservesFiniteLimits_lan`: the left Kan extension of abelian
  presheaves along `j.op` preserves finite limits.
* `Stacks.Sites.LocalizationShriek.preservesFiniteLimits_sheafPullback` and
  `Stacks.Sites.LocalizationShriek.preservesMonomorphisms_sheafPullback`: extension by zero is
  exact.
* `Stacks.Sites.LocalizationShriek.preservesInjectiveObjects_sheafPushforwardContinuous`:
  restriction to `C/K` preserves injective abelian sheaves.

## Implementation notes

Only the universes forced by the statement appear: the site has objects in `Type u` and
morphisms in `Type v`, the presheaf of sets and the abelian sheaves take values in `Type v`,
and `C/K` has objects in `Type (max u v)`. In particular `AddCommGrpCat.{v}` does *not* have
colimits of the size of `CostructuredArrow j.op U`; the colimits used here exist because the
diagrams are final over the discrete category on `K(U)`, whose index type is `Type v`. That is
why finality is proved before any colimit is formed.

Sheafification on `(C, J)` is an instance hypothesis rather than a consequence: for a site
whose objects live in a universe larger than the sheaf values it is not available, and nothing
here can produce it.

The special case `K = yoneda.obj U` is restriction to the slice site `C/U`, which is Stacks
03F3 (1) as the source states it; the fibrewise argument below is the same one in the
generality of an arbitrary presheaf of sets.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 07A0](https://stacks.math.columbia.edu/tag/07A0)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.Sites.LocalizationShriek

variable {C : Type u} [Category.{v} C] (K : Cᵒᵖ ⥤ Type v)

namespace Fiber

variable {K} in
/-- The section of `K` over `X` cut out by an object of the comma category
`CostructuredArrow (CostructuredArrow.proj yoneda K).op X`: the object is a pair `(V, s)`
together with a map `X.unop ⟶ V`, and the section is the pullback of `s` along that map. -/
def idx {X : Cᵒᵖ} (d : CostructuredArrow (CostructuredArrow.proj yoneda K).op X) : K.obj X :=
  K.map d.hom (yonedaEquiv d.left.unop.hom)

/-- The discrete category on `K(X)` sits in the comma category
`CostructuredArrow (CostructuredArrow.proj yoneda K).op X` by sending a section `t` to the pair
`(X.unop, t)` with the identity of `X.unop` as structure map. These are the objects with
initial fibre. -/
def functor (X : Cᵒᵖ) :
    Discrete (K.obj X) ⥤ CostructuredArrow (CostructuredArrow.proj yoneda K).op X :=
  Discrete.functor fun t =>
    CostructuredArrow.mk (Y := op (CostructuredArrow.mk (yonedaEquiv.symm t)))
      (op (𝟙 X.unop))

/-! `functor` must be reducible: the comparisons below ask whether the structure map of one of
its values is an identity and whether an index is a section of `K`, and both hold only by
unfolding it, which `rw` and instance search do not do at their own transparency. -/
attribute [local implicit_reducible] functor

variable {K}

/-- The underlying map of the structure morphism of an object of `StructuredArrow d (functor K X)`
is the structure map of `d`. -/
lemma hom_left_unop_left {X : Cᵒᵖ}
    {d : CostructuredArrow (CostructuredArrow.proj yoneda K).op X}
    (Z : StructuredArrow d (functor K X)) :
    (Z.hom.left.unop.left).op = d.hom := by
  have h : (Z.hom.left.unop.left).op ≫ op (𝟙 X.unop) = d.hom := CostructuredArrow.w Z.hom
  exact (Category.comp_id _).symm.trans h

/-- The structure map of `d`, read as a morphism of `C/K` into the pair `d` from the pair
`(X, idx d)`. -/
lemma yoneda_map_comp_hom {X : Cᵒᵖ}
    (d : CostructuredArrow (CostructuredArrow.proj yoneda K).op X) :
    yoneda.map d.hom.unop ≫ d.left.unop.hom = yonedaEquiv.symm (idx d) := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, idx, ← yonedaEquiv_naturality]
  rfl

/-- Every object of `StructuredArrow d (functor K X)` lies over the section cut out by `d`. -/
lemma idx_eq {X : Cᵒᵖ} {d : CostructuredArrow (CostructuredArrow.proj yoneda K).op X}
    (Z : StructuredArrow d (functor K X)) :
    Z.right.as = idx d := by
  have hw : yoneda.map Z.hom.left.unop.left ≫ d.left.unop.hom =
      yonedaEquiv.symm Z.right.as := CostructuredArrow.w Z.hom.left.unop
  have h2 : K.map (Z.hom.left.unop.left).op (yonedaEquiv d.left.unop.hom) = Z.right.as := by
    rw [yonedaEquiv_naturality, hw]
    exact Equiv.apply_symm_apply _ _
  conv_rhs => rw [idx, ← hom_left_unop_left Z]
  exact h2.symm

/-- The object of `StructuredArrow d (functor K X)` at the section cut out by `d`. -/
def initObj {X : Cᵒᵖ} (d : CostructuredArrow (CostructuredArrow.proj yoneda K).op X) :
    StructuredArrow d (functor K X) :=
  StructuredArrow.mk (Y := Discrete.mk (idx d))
    (CostructuredArrow.homMk
      (Quiver.Hom.op (CostructuredArrow.homMk d.hom.unop (yoneda_map_comp_hom d)))
      (by
        apply Quiver.Hom.unop_inj
        simp [functor]))

/-! `initObj` must be reducible for instance search and for the identity morphism of its index to
typecheck against the destructured form of an object of the comma category. -/
attribute [local implicit_reducible] initObj

/-- The unique morphism out of `initObj d`. There is only one, because a morphism of
`CostructuredArrow (CostructuredArrow.proj yoneda K).op X` into an object whose structure map is
an identity is determined by the structure map of its source. -/
def initHom {X : Cᵒᵖ} (d : CostructuredArrow (CostructuredArrow.proj yoneda K).op X)
    (Z : StructuredArrow d (functor K X)) : initObj d ⟶ Z := by
  obtain ⟨⟨⟨⟩⟩, ⟨t⟩, f⟩ := Z
  have ht : t = idx d := idx_eq (StructuredArrow.mk f)
  subst ht
  refine StructuredArrow.homMk (𝟙 _) ?_
  exact (Category.comp_id _).trans <| CostructuredArrow.hom_ext _ _ <| Quiver.Hom.unop_inj <|
    CostructuredArrow.hom_ext _ _
      (congrArg Quiver.Hom.unop (hom_left_unop_left (StructuredArrow.mk f))).symm

/-- `initObj d` is initial, so each comma category of `functor K X` is connected. -/
def isInitialInitObj {X : Cᵒᵖ}
    (d : CostructuredArrow (CostructuredArrow.proj yoneda K).op X) :
    IsInitial (initObj d) :=
  IsInitial.ofUniqueHom (initHom d) fun _ _ => StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)

/-- The discrete category on `K(X)` is final in
`CostructuredArrow (CostructuredArrow.proj yoneda K).op X`: the comma category of an object `d`
has `initObj d` as initial object. -/
instance final (K : Cᵒᵖ ⥤ Type v) (X : Cᵒᵖ) : (functor K X).Final :=
  Functor.Final.mk fun d => isConnected_of_isInitial _ (isInitialInitObj d)

end Fiber

section Lan

variable {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {E : Type*} [Category* E]

/-! `IsPointwiseLeftKanExtensionAt` is a semireducible `def` for `IsColimit` of the comma cocone,
so the colimit lemmas below, whose statements are about `IsColimit`, are invisible to `rw` at its
own transparency; it is made reducible locally. -/
attribute [local implicit_reducible]
  Functor.LeftExtension.IsPointwiseLeftKanExtensionAt Functor.lan

/-- The evaluation of a left Kan extension at an object is the colimit over the comma category of
costructured arrows, naturally in the functor being extended. This is
`CategoryTheory.lanEvaluationIsoColim` with no smallness hypothesis on the two source categories,
which is needed here because the site of elements of a presheaf of sets does not have its objects
in the universe of its morphisms. -/
noncomputable def lanCompEvaluationIsoColim (F : D₁ ⥤ D₂) (X : D₂)
    [∀ G : D₁ ⥤ E, F.HasPointwiseLeftKanExtension G]
    [∀ Y : D₂, HasColimitsOfShape (CostructuredArrow F Y) E] :
    F.lan ⋙ (evaluation D₂ E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G => F.leftKanExtensionObjIsoColimit G X) (fun {G₁ G₂} φ => by
    have hunit : ∀ T : CostructuredArrow F X,
        (F.leftKanExtensionUnit G₁).app T.left ≫ (F.lan.map φ).app (F.obj T.left) =
          φ.app T.left ≫ (F.leftKanExtensionUnit G₂).app T.left := fun T =>
      (Functor.descOfIsLeftKanExtension_fac_app (F.leftKanExtension G₁)
        (F.leftKanExtensionUnit G₁) (F.leftKanExtension G₂)
        (φ ≫ F.leftKanExtensionUnit G₂) T.left).trans
        (NatTrans.comp_app φ (F.leftKanExtensionUnit G₂) T.left)
    have key : (F.leftKanExtensionObjIsoColimit G₁ X).inv ≫
        ((F.lan.map φ).app X ≫ (F.leftKanExtensionObjIsoColimit G₂ X).hom) =
        (F.leftKanExtensionObjIsoColimit G₁ X).inv ≫
          ((F.leftKanExtensionObjIsoColimit G₁ X).hom ≫
            colimMap ((CostructuredArrow.proj F X).whiskerLeft φ)) := by
      apply colimit.hom_ext
      intro T
      have hRHS : colimit.ι (CostructuredArrow.proj F X ⋙ G₁) T ≫
          (F.leftKanExtensionObjIsoColimit G₁ X).inv ≫
            (F.leftKanExtensionObjIsoColimit G₁ X).hom ≫
              colimMap ((CostructuredArrow.proj F X).whiskerLeft φ) =
          φ.app T.left ≫ colimit.ι (CostructuredArrow.proj F X ⋙ G₂) T := by
        simp
      rw [Functor.ι_leftKanExtensionObjIsoColimit_inv_assoc, NatTrans.naturality_assoc,
        reassoc_of% (hunit T)]
      refine Eq.trans ?_ hRHS.symm
      exact congrArg (fun g => φ.app T.left ≫ g)
        (Functor.ι_leftKanExtensionObjIsoColimit_hom F G₂ X T)
    exact (Iso.cancel_iso_inv_left _ _ _).1 key)

end Lan

section Exactness

/-- Colimits indexed by the comma category of costructured arrows of `j.op` over `X` exist in
abelian groups even though that comma category is not small relative to them: the diagrams are
final over the discrete category on `K(X)`, whose index type is the sections of `K`. -/
instance hasColimitsOfShape_costructuredArrow (X : Cᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (CostructuredArrow.proj yoneda K).op X)
      AddCommGrpCat.{v} :=
  Functor.Final.hasColimitsOfShape_of_final (Fiber.functor K X)

/-- Left Kan extension of abelian presheaves along `j.op` is computed pointwise. -/
instance hasPointwiseLeftKanExtension
    (P : (CostructuredArrow (yoneda (C := C)) K)ᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (CostructuredArrow.proj yoneda K).op.HasPointwiseLeftKanExtension P :=
  fun _ => inferInstance

/-- Colimits of that shape in abelian groups are exact: they are coproducts indexed by the
sections of `K`, by finality of the discrete fibre, and coproducts of abelian groups are exact
(Grothendieck's axiom AB4). -/
theorem hasExactColimitsOfShape_costructuredArrow (X : Cᵒᵖ) :
    HasExactColimitsOfShape (CostructuredArrow (CostructuredArrow.proj yoneda K).op X)
      AddCommGrpCat.{v} :=
  hasExactColimitsOfShape_of_final AddCommGrpCat.{v} (Fiber.functor K X)

/-- The left Kan extension of abelian presheaves along `j.op` preserves finite limits. This is the
analytic content of the exactness of extension by zero. -/
theorem preservesFiniteLimits_lan :
    PreservesFiniteLimits ((CostructuredArrow.proj (yoneda (C := C)) K).op.lan :
      ((CostructuredArrow yoneda K)ᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{v})) := by
  apply preservesFiniteLimits_of_evaluation
  intro X
  have := hasExactColimitsOfShape_costructuredArrow K X
  have : PreservesFiniteLimits
      (colim (J := CostructuredArrow (CostructuredArrow.proj (yoneda (C := C)) K).op X)
        (C := AddCommGrpCat.{v})) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  exact preservesFiniteLimits_of_natIso
    (lanCompEvaluationIsoColim (E := AddCommGrpCat.{v})
      (CostructuredArrow.proj (yoneda (C := C)) K).op X).symm

end Exactness

section Injectives

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]
  [(CostructuredArrow.proj yoneda K).IsContinuous
    ((CostructuredArrow.proj yoneda K).restrictedTopology J) J]

omit [(CostructuredArrow.proj yoneda K).IsContinuous
  ((CostructuredArrow.proj yoneda K).restrictedTopology J) J] in
/-- **Stacks 03DJ for a presheaf of sets.** Extension by zero from the site of elements of `K` to
`C` preserves finite limits: it is the left Kan extension along `j.op`, which is left exact, read
between sheaves through sheafification, which is left exact too. -/
theorem preservesFiniteLimits_sheafPullback :
    PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (CostructuredArrow.proj (yoneda (C := C)) K) AddCommGrpCat.{v}
      ((CostructuredArrow.proj yoneda K).restrictedTopology J) J) := by
  have := preservesFiniteLimits_lan K
  exact comp_preservesFiniteLimits _ _

omit [(CostructuredArrow.proj yoneda K).IsContinuous
  ((CostructuredArrow.proj yoneda K).restrictedTopology J) J] in
/-- Extension by zero preserves monomorphisms, being left exact. -/
theorem preservesMonomorphisms_sheafPullback :
    (Functor.sheafPullbackConstruction.sheafPullback
      (CostructuredArrow.proj (yoneda (C := C)) K) AddCommGrpCat.{v}
      ((CostructuredArrow.proj yoneda K).restrictedTopology J) J).PreservesMonomorphisms :=
  have := preservesFiniteLimits_sheafPullback K J
  preservesMonomorphisms_of_preservesLimitsOfShape _

/-- **Stacks 03F3 (1), for a presheaf of sets in place of an object of the site, and so Stacks
07A0's first assertion.** Restriction of abelian sheaves along the projection `j` from the site of
elements of `K` — the inverse image `j⁻¹` of the localization morphism of topoi — preserves
injective objects. Its left adjoint is extension by zero, which is exact.

Stacks 03F3 (1) itself is the statement for sheaves of modules over a sheaf of rings, which is a
different category; it is
`Stacks.Cohomology.Localization.preservesInjectiveObjects_overFunctor`. -/
@[sga "4 V 2.2" "special case", sga "4 V 2.3.2" "special case", sga "4 V 4.11" "1), special case"]
theorem preservesInjectiveObjects_sheafPushforwardContinuous :
    ((CostructuredArrow.proj (yoneda (C := C)) K).sheafPushforwardContinuous AddCommGrpCat.{v}
      ((CostructuredArrow.proj yoneda K).restrictedTopology J) J).PreservesInjectiveObjects :=
  have := preservesMonomorphisms_sheafPullback K J
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (CostructuredArrow.proj (yoneda (C := C)) K) AddCommGrpCat.{v}
      ((CostructuredArrow.proj yoneda K).restrictedTopology J) J)

/-- An injective abelian sheaf on `C` restricts to an injective abelian sheaf on the site of
elements of `K`. -/
@[sga "4 V 2.3.2" "special case"]
theorem injective_sheafPushforwardContinuous_obj (I : Sheaf J AddCommGrpCat.{v}) [Injective I] :
    Injective (((CostructuredArrow.proj (yoneda (C := C)) K).sheafPushforwardContinuous
      AddCommGrpCat.{v} ((CostructuredArrow.proj yoneda K).restrictedTopology J) J).obj I) :=
  have := preservesInjectiveObjects_sheafPushforwardContinuous K J
  Functor.injective_obj _ _

end Injectives

section SheafOfSets

/-- **Stacks 07A0, first assertion.** For a *sheaf* of sets `K`, the projection `j` from the site
of elements of `K` is continuous for the restricted topology (Stacks 0791), so that restriction of
abelian sheaves along it is the inverse image of the localization morphism of topoi
`j : Sh(C/K) ⟶ Sh(C)`; that inverse image preserves injective abelian sheaves.

The continuity instance is the one Stacks 0791 provides, so the functor here is literally the
inverse image of the localization morphism and not merely isomorphic to it. -/
@[stacks 07A0 "the inverse image preserves injectives"]
theorem preservesInjectiveObjects_sheafLocalizationInverseImage
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}] (K : Sheaf J (Type v)) :
    letI : (CostructuredArrow.proj yoneda K.obj).IsContinuous
        ((CostructuredArrow.proj yoneda K.obj).restrictedTopology J) J :=
      (K.property.exists_sheafEquivalence_costructuredArrow_yoneda).2.2.choose
    ((CostructuredArrow.proj yoneda K.obj).sheafPushforwardContinuous AddCommGrpCat.{v}
        ((CostructuredArrow.proj yoneda K.obj).restrictedTopology J)
        J).PreservesInjectiveObjects :=
  let : (CostructuredArrow.proj yoneda K.obj).IsContinuous
      ((CostructuredArrow.proj yoneda K.obj).restrictedTopology J) J :=
    (K.property.exists_sheafEquivalence_costructuredArrow_yoneda).2.2.choose
  preservesInjectiveObjects_sheafPushforwardContinuous K.obj J

end SheafOfSets

end Stacks.Sites.LocalizationShriek

end
