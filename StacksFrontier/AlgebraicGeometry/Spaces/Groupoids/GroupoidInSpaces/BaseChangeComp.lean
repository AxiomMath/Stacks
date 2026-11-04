module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces.BaseChange

/-!
# Composing two base changes of a groupoid in algebraic spaces

Base changing a groupoid along `B' ⟶ B` and then along `B'' ⟶ B'` is base changing it along the
composite, as an isomorphism `AlgebraicGeometry.Space.baseChangeCompIso` of groupoids in algebraic
spaces over `B''`. Along the way, isomorphisms of groupoids in algebraic spaces over a fixed base,
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Iso`, and the constructors
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mk'` and `…Iso.mk'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### Composing two base changes of a groupoid

Base changing a groupoid along `h : B' ⟶ B` and then along `k : B'' ⟶ B'` gives the same thing as
base changing along `k ≫ h`, up to the comparison of iterated fibre products
`CategoryTheory.Limits.pullbackRightPullbackFstIso`. The object and arrow spaces are compared by
that isomorphism on the nose, and the lemma below says the comparison carries the structure
morphism of the twice-base-changed groupoid to that of the once-base-changed one.

The proof is written in term mode rather than with `rw` or `simp`: the goals
`CategoryTheory.Limits.pullback.hom_ext` produces here mix `pullback (k.hom ≫ h.hom) …` with
`(baseChange G (k ≫ h)).groupoid.arrows.obj`, which are definitionally but not syntactically
equal, and a rewrite motive against them is rejected at `implicit` transparency.

**What does work on goals of this shape, and why.** Two reductions are `rfl` here: applying a
composite of natural transformations, `(α ≫ β).app T x = β.app T (α.app T x)`, and the underlying
presheaf morphism of a composite of morphisms of algebraic spaces, `(f ≫ g).hom = f.hom ≫ g.hom`.
So a chain of *element* equations whose steps are `congrArg (fun m => m.app T x) e`, for `e` a
morphism equation, typechecks against any `have` or `calc` type that is definitionally what
`congrArg` produces, and no rewrite motive is ever formed — the elaborator is only ever asked to
check a defeq, which it does. That is how
`AlgebraicGeometry.Space.pullbackRightPullbackFstIso_hom_baseChange_map_comp` below and the
pointwise clauses of `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Iso.mk'` are proved, and it is
why they go through where the composite-level route, which does form such motives, does not.

The one remaining subtlety is spelling. `φ.toGroupoidHom.mapObjects` has type
`G.toGroupoidInFunctors.objects ⟶ …`, while in a composite written `G.source.hom ≫
φ.toGroupoidHom.mapObjects` the elaborated `≫` takes its domain from `G.source.hom` and so reads
`G.objects.obj ⟶ …`. The two are definitionally equal and syntactically different, so a `rw` with
a hypothesis stated in one spelling does not fire against the other. Working pointwise avoids this
as well, since `congrArg` never has to match a pattern.
-/

/-- The comparison of iterated fibre products carries one structure map (source or target) of the
twice-base-changed groupoid to that of the once-base-changed one, given the projection identities
of each. -/
private theorem pullbackRightPullbackFstIso_hom_comp_map_of_proj
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B B' B'' : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
    (h : B' ⟶ B) (k : B'' ⟶ B')
    (p : G.arrows.obj ⟶ G.objects.obj)
    (q : pullback h.hom G.arrowsToBase.hom ⟶ pullback h.hom G.objectsToBase.hom)
    (s2 : pullback k.hom (pullback.fst h.hom G.arrowsToBase.hom) ⟶
      pullback k.hom (pullback.fst h.hom G.objectsToBase.hom))
    (s3 : pullback (k.hom ≫ h.hom) G.arrowsToBase.hom ⟶
      pullback (k.hom ≫ h.hom) G.objectsToBase.hom)
    (e1 : s3 ≫ pullback.fst (k.hom ≫ h.hom) G.objectsToBase.hom =
      pullback.fst (k.hom ≫ h.hom) G.arrowsToBase.hom)
    (e1' : s3 ≫ pullback.snd (k.hom ≫ h.hom) G.objectsToBase.hom =
      pullback.snd (k.hom ≫ h.hom) G.arrowsToBase.hom ≫ p)
    (e4 : s2 ≫ pullback.fst k.hom (pullback.fst h.hom G.objectsToBase.hom) =
      pullback.fst k.hom (pullback.fst h.hom G.arrowsToBase.hom))
    (e4' : s2 ≫ pullback.snd k.hom (pullback.fst h.hom G.objectsToBase.hom) =
      pullback.snd k.hom (pullback.fst h.hom G.arrowsToBase.hom) ≫ q)
    (e5 : q ≫ pullback.snd h.hom G.objectsToBase.hom =
      pullback.snd h.hom G.arrowsToBase.hom ≫ p) :
    (pullbackRightPullbackFstIso h.hom G.arrowsToBase.hom k.hom).hom ≫ s3 =
      s2 ≫ (pullbackRightPullbackFstIso h.hom G.objectsToBase.hom k.hom).hom :=
  let ia := (pullbackRightPullbackFstIso h.hom G.arrowsToBase.hom k.hom).hom
  let io := (pullbackRightPullbackFstIso h.hom G.objectsToBase.hom k.hom).hom
  have ea : ia ≫ pullback.fst (k.hom ≫ h.hom) G.arrowsToBase.hom =
      pullback.fst k.hom (pullback.fst h.hom G.arrowsToBase.hom) :=
    pullbackRightPullbackFstIso_hom_fst _ _ _
  have eo : io ≫ pullback.fst (k.hom ≫ h.hom) G.objectsToBase.hom =
      pullback.fst k.hom (pullback.fst h.hom G.objectsToBase.hom) :=
    pullbackRightPullbackFstIso_hom_fst _ _ _
  have eas : ia ≫ pullback.snd (k.hom ≫ h.hom) G.arrowsToBase.hom =
      pullback.snd k.hom (pullback.fst h.hom G.arrowsToBase.hom) ≫
        pullback.snd h.hom G.arrowsToBase.hom :=
    pullbackRightPullbackFstIso_hom_snd _ _ _
  have eos : io ≫ pullback.snd (k.hom ≫ h.hom) G.objectsToBase.hom =
      pullback.snd k.hom (pullback.fst h.hom G.objectsToBase.hom) ≫
        pullback.snd h.hom G.objectsToBase.hom :=
    pullbackRightPullbackFstIso_hom_snd _ _ _
  pullback.hom_ext
    ((Category.assoc ia s3 _).trans
      (((congrArg (fun m => ia ≫ m) e1).trans ea).trans
        ((((congrArg (fun m => s2 ≫ m) eo).trans e4).symm).trans
          (Category.assoc s2 io _).symm)))
    ((Category.assoc ia s3 _).trans
      (((congrArg (fun m => ia ≫ m) e1').trans
        (((Category.assoc ia _ p).symm.trans
          (congrArg (fun m => m ≫ p) eas)).trans
          ((Category.assoc _ _ p).trans
            ((congrArg (fun m => pullback.snd k.hom (pullback.fst h.hom G.arrowsToBase.hom) ≫ m)
              e5.symm).trans
              (((Category.assoc _ _ _).symm.trans
                (congrArg (fun m => m ≫ pullback.snd h.hom G.objectsToBase.hom) e4'.symm)).trans
                ((Category.assoc s2 _ _).trans
                  (congrArg (fun m => s2 ≫ m) eos.symm))))))).trans
        (Category.assoc s2 io _).symm))

/-- The comparison of iterated fibre products carries the source of the twice-base-changed
groupoid to the source of the once-base-changed one. -/
theorem pullbackRightPullbackFstIso_hom_comp_baseChange_source
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B B' B'' : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
    (h : B' ⟶ B) (k : B'' ⟶ B') :
    (pullbackRightPullbackFstIso h.hom G.arrowsToBase.hom k.hom).hom ≫
        (baseChange G (k ≫ h)).groupoid.source.hom =
      (baseChange (baseChange G h).groupoid k).groupoid.source.hom ≫
        (pullbackRightPullbackFstIso h.hom G.objectsToBase.hom k.hom).hom :=
  pullbackRightPullbackFstIso_hom_comp_map_of_proj G h k G.source.hom
    (baseChange G h).groupoid.source.hom
    (baseChange (baseChange G h).groupoid k).groupoid.source.hom
    (baseChange G (k ≫ h)).groupoid.source.hom
    (baseChange_source_comp_fst G (k ≫ h)) (baseChange_source_comp_snd G (k ≫ h))
    (baseChange_source_comp_fst (baseChange G h).groupoid k)
    (baseChange_source_comp_snd (baseChange G h).groupoid k) (baseChange_source_comp_snd G h)

/-- The comparison of iterated fibre products carries the target of the twice-base-changed
groupoid to the target of the once-base-changed one. -/
theorem pullbackRightPullbackFstIso_hom_comp_baseChange_target
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B B' B'' : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
    (h : B' ⟶ B) (k : B'' ⟶ B') :
    (pullbackRightPullbackFstIso h.hom G.arrowsToBase.hom k.hom).hom ≫
        (baseChange G (k ≫ h)).groupoid.target.hom =
      (baseChange (baseChange G h).groupoid k).groupoid.target.hom ≫
        (pullbackRightPullbackFstIso h.hom G.objectsToBase.hom k.hom).hom :=
  pullbackRightPullbackFstIso_hom_comp_map_of_proj G h k G.target.hom
    (baseChange G h).groupoid.target.hom
    (baseChange (baseChange G h).groupoid k).groupoid.target.hom
    (baseChange G (k ≫ h)).groupoid.target.hom
    (baseChange_target_comp_fst G (k ≫ h)) (baseChange_target_comp_snd G (k ≫ h))
    (baseChange_target_comp_fst (baseChange G h).groupoid k)
    (baseChange_target_comp_snd (baseChange G h).groupoid k) (baseChange_target_comp_snd G h)

/-- The first projection of the fibre product sends a composable pair to its first arrow. -/
private theorem pullback_fst_app_composableToPullback {U R : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (s t : R ⟶ U) (T : (BigFppfOver C S hS)ᵒᵖ) (a b : R.obj T) (hab : s.app T a = t.app T b) :
    (pullback.fst s t).app T ((composableToPullback s t).app T ⟨(a, b), hab⟩) = a := by
  change ((composableToPullback s t ≫ pullback.fst s t).app T) ⟨(a, b), hab⟩ = a
  rw [composableToPullback, pullback.lift_fst]
  rfl

/-- The second projection of the fibre product sends a composable pair to its second arrow. -/
private theorem pullback_snd_app_composableToPullback {U R : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (s t : R ⟶ U) (T : (BigFppfOver C S hS)ᵒᵖ) (a b : R.obj T) (hab : s.app T a = t.app T b) :
    (pullback.snd s t).app T ((composableToPullback s t).app T ⟨(a, b), hab⟩) = b := by
  change ((composableToPullback s t ≫ pullback.snd s t).app T) ⟨(a, b), hab⟩ = b
  rw [composableToPullback, pullback.lift_snd]
  rfl

/-- **The comparison of iterated fibre products carries the composition law of the
twice-base-changed groupoid to that of the once-base-changed one.** With
`AlgebraicGeometry.Space.pullbackRightPullbackFstIso_hom_comp_baseChange_source` and `…_target`
this is everything `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mk'` asks for, the identity
law not being a hypothesis there.

Which proof `hab'` of the composability of the two image arrows is supplied does not matter;
`AlgebraicGeometry.Space.baseChangeCompHom` supplies the one
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mk'` builds out of the source and target clauses.

Neither composition law can be computed — each is a nested `CategoryTheory.IsPullback.lift` — so
what is compared instead are the two projections of each, by
`AlgebraicGeometry.Space.fiberProductAtEquiv`: the point of the new base, which both sides take
from the first arrow, and the old arrow, which on both sides is the composite in the original
groupoid of the two old arrows underlying the pair. The latter needs the two composable-pair
comparisons to agree, which is the inner `hToOld`. -/
theorem pullbackRightPullbackFstIso_hom_baseChange_map_comp
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B B' B'' : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (h : B' ⟶ B) (k : B'' ⟶ B')
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : (baseChange (baseChange G h).groupoid k).groupoid.arrows.obj.obj T)
    (hab : (baseChange (baseChange G h).groupoid k).groupoid.source.hom.app T a =
      (baseChange (baseChange G h).groupoid k).groupoid.target.hom.app T b)
    (hab' : (baseChange G (k ≫ h)).groupoid.source.hom.app T
        ((pullbackRightPullbackFstIso h.hom G.arrowsToBase.hom k.hom).hom.app T a) =
      (baseChange G (k ≫ h)).groupoid.target.hom.app T
        ((pullbackRightPullbackFstIso h.hom G.arrowsToBase.hom k.hom).hom.app T b)) :
    (baseChange G (k ≫ h)).groupoid.toGroupoidInFunctors.compose T
        ((pullbackRightPullbackFstIso h.hom G.arrowsToBase.hom k.hom).hom.app T a)
        ((pullbackRightPullbackFstIso h.hom G.arrowsToBase.hom k.hom).hom.app T b) hab' =
      (pullbackRightPullbackFstIso h.hom G.arrowsToBase.hom k.hom).hom.app T
        ((baseChange (baseChange G h).groupoid k).groupoid.toGroupoidInFunctors.compose
          T a b hab) := by
  let A := G.arrowsToBase.hom
  let G₁ := (baseChange G h).groupoid
  let G₂ := (baseChange G₁ k).groupoid
  let G₃ := (baseChange G (k ≫ h)).groupoid
  let ia := (pullbackRightPullbackFstIso h.hom A k.hom).hom
  let toOld₁ := baseChangeComposableToOld G h
  let toOld₂ := baseChangeComposableToOld G₁ k
  let toOld₃ := baseChangeComposableToOld G (k ≫ h)
  let c₂ : (pullback G₂.source.hom G₂.target.hom).obj T :=
    (composableToPullback G₂.source.hom G₂.target.hom).app T ⟨(a, b), hab⟩
  let c₃ : (pullback G₃.source.hom G₃.target.hom).obj T :=
    (composableToPullback G₃.source.hom G₃.target.hom).app T
      ⟨(ia.app T a, ia.app T b), hab'⟩
  have hc₂fst : (pullback.fst G₂.source.hom G₂.target.hom).app T c₂ = a :=
    pullback_fst_app_composableToPullback _ _ T a b hab
  have hc₂snd : (pullback.snd G₂.source.hom G₂.target.hom).app T c₂ = b :=
    pullback_snd_app_composableToPullback _ _ T a b hab
  have hc₃fst : (pullback.fst G₃.source.hom G₃.target.hom).app T c₃ = ia.app T a :=
    pullback_fst_app_composableToPullback _ _ T _ _ hab'
  have hc₃snd : (pullback.snd G₃.source.hom G₃.target.hom).app T c₃ = ia.app T b :=
    pullback_snd_app_composableToPullback _ _ T _ _ hab'
  have e3fst : G₃.comp.hom ≫ pullback.fst (k.hom ≫ h.hom) A =
      pullback.fst G₃.source.hom G₃.target.hom ≫ pullback.fst (k.hom ≫ h.hom) A :=
    baseChange_comp_comp_fst G (k ≫ h)
  have e3snd : G₃.comp.hom ≫ pullback.snd (k.hom ≫ h.hom) A = toOld₃.hom ≫ G.comp.hom :=
    baseChange_comp_comp_snd G (k ≫ h)
  have e2fst : G₂.comp.hom ≫ pullback.fst k.hom (pullback.fst h.hom A) =
      pullback.fst G₂.source.hom G₂.target.hom ≫
        pullback.fst k.hom (pullback.fst h.hom A) :=
    baseChange_comp_comp_fst G₁ k
  have e2snd : G₂.comp.hom ≫ pullback.snd k.hom (pullback.fst h.hom A) =
      toOld₂.hom ≫ G₁.comp.hom :=
    baseChange_comp_comp_snd G₁ k
  have e1snd : G₁.comp.hom ≫ pullback.snd h.hom A = toOld₁.hom ≫ G.comp.hom :=
    baseChange_comp_comp_snd G h
  have t3fst : toOld₃.hom ≫ pullback.fst G.source.hom G.target.hom =
      pullback.fst G₃.source.hom G₃.target.hom ≫ pullback.snd (k.hom ≫ h.hom) A :=
    baseChangeComposableToOld_comp_fst G (k ≫ h)
  have t3snd : toOld₃.hom ≫ pullback.snd G.source.hom G.target.hom =
      pullback.snd G₃.source.hom G₃.target.hom ≫ pullback.snd (k.hom ≫ h.hom) A :=
    baseChangeComposableToOld_comp_snd G (k ≫ h)
  have t2fst : toOld₂.hom ≫ pullback.fst G₁.source.hom G₁.target.hom =
      pullback.fst G₂.source.hom G₂.target.hom ≫
        pullback.snd k.hom (pullback.fst h.hom A) :=
    baseChangeComposableToOld_comp_fst G₁ k
  have t2snd : toOld₂.hom ≫ pullback.snd G₁.source.hom G₁.target.hom =
      pullback.snd G₂.source.hom G₂.target.hom ≫
        pullback.snd k.hom (pullback.fst h.hom A) :=
    baseChangeComposableToOld_comp_snd G₁ k
  have t1fst : toOld₁.hom ≫ pullback.fst G.source.hom G.target.hom =
      pullback.fst G₁.source.hom G₁.target.hom ≫ pullback.snd h.hom A :=
    baseChangeComposableToOld_comp_fst G h
  have t1snd : toOld₁.hom ≫ pullback.snd G.source.hom G.target.hom =
      pullback.snd G₁.source.hom G₁.target.hom ≫ pullback.snd h.hom A :=
    baseChangeComposableToOld_comp_snd G h
  have iafst : ia ≫ pullback.fst (k.hom ≫ h.hom) A =
      pullback.fst k.hom (pullback.fst h.hom A) :=
    pullbackRightPullbackFstIso_hom_fst _ _ _
  have iasnd : ia ≫ pullback.snd (k.hom ≫ h.hom) A =
      pullback.snd k.hom (pullback.fst h.hom A) ≫ pullback.snd h.hom A :=
    pullbackRightPullbackFstIso_hom_snd _ _ _
  have hToOld : toOld₃.hom.app T c₃ = toOld₁.hom.app T (toOld₂.hom.app T c₂) := by
    apply (fiberProductAtEquiv G.source G.target T).injective
    apply Subtype.ext
    apply Prod.ext
    · calc (fiberProductAtEquiv G.source G.target T (toOld₃.hom.app T c₃)).val.1
          = (pullback.fst G.source.hom G.target.hom).app T (toOld₃.hom.app T c₃) :=
            fiberProductAtEquiv_fst G.source G.target T _
        _ = (pullback.snd (k.hom ≫ h.hom) A).app T
              ((pullback.fst G₃.source.hom G₃.target.hom).app T c₃) :=
            congrArg (fun m => m.app T c₃) t3fst
        _ = (pullback.snd (k.hom ≫ h.hom) A).app T (ia.app T a) :=
            congrArg (fun z => (pullback.snd (k.hom ≫ h.hom) A).app T z) hc₃fst
        _ = (pullback.snd h.hom A).app T
              ((pullback.snd k.hom (pullback.fst h.hom A)).app T a) :=
            congrArg (fun m => m.app T a) iasnd
        _ = (pullback.snd h.hom A).app T
              ((pullback.snd k.hom (pullback.fst h.hom A)).app T
                ((pullback.fst G₂.source.hom G₂.target.hom).app T c₂)) :=
            congrArg (fun z => (pullback.snd h.hom A).app T
              ((pullback.snd k.hom (pullback.fst h.hom A)).app T z)) hc₂fst.symm
        _ = (pullback.snd h.hom A).app T
              ((pullback.fst G₁.source.hom G₁.target.hom).app T (toOld₂.hom.app T c₂)) :=
            congrArg (fun z => (pullback.snd h.hom A).app T z)
              (congrArg (fun m => m.app T c₂) t2fst).symm
        _ = (pullback.fst G.source.hom G.target.hom).app T
              (toOld₁.hom.app T (toOld₂.hom.app T c₂)) :=
            (congrArg (fun m => m.app T (toOld₂.hom.app T c₂)) t1fst).symm
        _ = (fiberProductAtEquiv G.source G.target T
              (toOld₁.hom.app T (toOld₂.hom.app T c₂))).val.1 :=
            (fiberProductAtEquiv_fst G.source G.target T _).symm
    · calc (fiberProductAtEquiv G.source G.target T (toOld₃.hom.app T c₃)).val.2
          = (pullback.snd G.source.hom G.target.hom).app T (toOld₃.hom.app T c₃) :=
            fiberProductAtEquiv_snd G.source G.target T _
        _ = (pullback.snd (k.hom ≫ h.hom) A).app T
              ((pullback.snd G₃.source.hom G₃.target.hom).app T c₃) :=
            congrArg (fun m => m.app T c₃) t3snd
        _ = (pullback.snd (k.hom ≫ h.hom) A).app T (ia.app T b) :=
            congrArg (fun z => (pullback.snd (k.hom ≫ h.hom) A).app T z) hc₃snd
        _ = (pullback.snd h.hom A).app T
              ((pullback.snd k.hom (pullback.fst h.hom A)).app T b) :=
            congrArg (fun m => m.app T b) iasnd
        _ = (pullback.snd h.hom A).app T
              ((pullback.snd k.hom (pullback.fst h.hom A)).app T
                ((pullback.snd G₂.source.hom G₂.target.hom).app T c₂)) :=
            congrArg (fun z => (pullback.snd h.hom A).app T
              ((pullback.snd k.hom (pullback.fst h.hom A)).app T z)) hc₂snd.symm
        _ = (pullback.snd h.hom A).app T
              ((pullback.snd G₁.source.hom G₁.target.hom).app T (toOld₂.hom.app T c₂)) :=
            congrArg (fun z => (pullback.snd h.hom A).app T z)
              (congrArg (fun m => m.app T c₂) t2snd).symm
        _ = (pullback.snd G.source.hom G.target.hom).app T
              (toOld₁.hom.app T (toOld₂.hom.app T c₂)) :=
            (congrArg (fun m => m.app T (toOld₂.hom.app T c₂)) t1snd).symm
        _ = (fiberProductAtEquiv G.source G.target T
              (toOld₁.hom.app T (toOld₂.hom.app T c₂))).val.2 :=
            (fiberProductAtEquiv_snd G.source G.target T _).symm
  have hmain : G₃.comp.hom.app T c₃ = ia.app T (G₂.comp.hom.app T c₂) := by
    apply (fiberProductAtEquiv (k ≫ h) G.arrowsToBase T).injective
    apply Subtype.ext
    apply Prod.ext
    · calc (fiberProductAtEquiv (k ≫ h) G.arrowsToBase T (G₃.comp.hom.app T c₃)).val.1
          = (pullback.fst (k.hom ≫ h.hom) A).app T (G₃.comp.hom.app T c₃) :=
            fiberProductAtEquiv_fst (k ≫ h) G.arrowsToBase T _
        _ = (pullback.fst (k.hom ≫ h.hom) A).app T
              ((pullback.fst G₃.source.hom G₃.target.hom).app T c₃) :=
            congrArg (fun m => m.app T c₃) e3fst
        _ = (pullback.fst (k.hom ≫ h.hom) A).app T (ia.app T a) :=
            congrArg (fun z => (pullback.fst (k.hom ≫ h.hom) A).app T z) hc₃fst
        _ = (pullback.fst k.hom (pullback.fst h.hom A)).app T a :=
            congrArg (fun m => m.app T a) iafst
        _ = (pullback.fst k.hom (pullback.fst h.hom A)).app T
              ((pullback.fst G₂.source.hom G₂.target.hom).app T c₂) :=
            congrArg (fun z => (pullback.fst k.hom (pullback.fst h.hom A)).app T z)
              hc₂fst.symm
        _ = (pullback.fst k.hom (pullback.fst h.hom A)).app T (G₂.comp.hom.app T c₂) :=
            (congrArg (fun m => m.app T c₂) e2fst).symm
        _ = (pullback.fst (k.hom ≫ h.hom) A).app T (ia.app T (G₂.comp.hom.app T c₂)) :=
            (congrArg (fun m => m.app T (G₂.comp.hom.app T c₂)) iafst).symm
        _ = (fiberProductAtEquiv (k ≫ h) G.arrowsToBase T
              (ia.app T (G₂.comp.hom.app T c₂))).val.1 :=
            (fiberProductAtEquiv_fst (k ≫ h) G.arrowsToBase T _).symm
    · calc (fiberProductAtEquiv (k ≫ h) G.arrowsToBase T (G₃.comp.hom.app T c₃)).val.2
          = (pullback.snd (k.hom ≫ h.hom) A).app T (G₃.comp.hom.app T c₃) :=
            fiberProductAtEquiv_snd (k ≫ h) G.arrowsToBase T _
        _ = G.comp.hom.app T (toOld₃.hom.app T c₃) :=
            congrArg (fun m => m.app T c₃) e3snd
        _ = G.comp.hom.app T (toOld₁.hom.app T (toOld₂.hom.app T c₂)) :=
            congrArg (fun z => G.comp.hom.app T z) hToOld
        _ = (pullback.snd h.hom A).app T (G₁.comp.hom.app T (toOld₂.hom.app T c₂)) :=
            (congrArg (fun m => m.app T (toOld₂.hom.app T c₂)) e1snd).symm
        _ = (pullback.snd h.hom A).app T
              ((pullback.snd k.hom (pullback.fst h.hom A)).app T (G₂.comp.hom.app T c₂)) :=
            congrArg (fun z => (pullback.snd h.hom A).app T z)
              (congrArg (fun m => m.app T c₂) e2snd).symm
        _ = (pullback.snd (k.hom ≫ h.hom) A).app T (ia.app T (G₂.comp.hom.app T c₂)) :=
            (congrArg (fun m => m.app T (G₂.comp.hom.app T c₂)) iasnd).symm
        _ = (fiberProductAtEquiv (k ≫ h) G.arrowsToBase T
              (ia.app T (G₂.comp.hom.app T c₂))).val.2 :=
            (fiberProductAtEquiv_snd (k ≫ h) G.arrowsToBase T _).symm
  exact hmain

end Space

/-! ### Isomorphisms of groupoids over a fixed base

These sit here, rather than beside `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom`, because the
constructor below discharges the identity law through
`AlgebraicGeometry.Space.mapIdentityOfMapComp`, which is proved above.
-/

namespace GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **A morphism of groupoids in algebraic spaces over `B`, from its two maps and their
compatibility with source, target and composition.** The identity law of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom` is *not* a hypothesis: identities in a groupoid
are determined by the composition law, so it follows from the other three by
`AlgebraicGeometry.Space.mapIdentityOfMapComp`.

This is the discharge `AlgebraicGeometry.Space.baseChange` performs inline for its own
projection, packaged so that a further construction of a morphism of groupoids need not repeat
it. -/
noncomputable def Hom.mk' {G H : GroupoidInAlgebraicSpaces C S hS B}
    (mapObjects : G.objects.obj ⟶ H.objects.obj)
    (mapArrows : G.arrows.obj ⟶ H.arrows.obj)
    (map_source : ∀ T a, H.source.hom.app T (mapArrows.app T a) =
      mapObjects.app T (G.source.hom.app T a))
    (map_target : ∀ T a, H.target.hom.app T (mapArrows.app T a) =
      mapObjects.app T (G.target.hom.app T a))
    (map_comp : ∀ T a b h,
      H.toGroupoidInFunctors.compose T (mapArrows.app T a) (mapArrows.app T b)
          ((map_source T a).trans ((congrArg (mapObjects.app T) h).trans
            (map_target T b).symm)) =
        mapArrows.app T (G.toGroupoidInFunctors.compose T a b h))
    (mapObjects_over : mapObjects ≫ H.objectsToBase.hom = G.objectsToBase.hom)
    (mapArrows_over : mapArrows ≫ H.arrowsToBase.hom = G.arrowsToBase.hom) :
    Hom G H where
  toGroupoidHom :=
    { mapObjects := mapObjects
      mapArrows := mapArrows
      map_source := map_source
      map_target := map_target
      map_id := Space.mapIdentityOfMapComp
        (G := G.toGroupoidInFunctors) (H := H.toGroupoidInFunctors)
        mapObjects mapArrows map_source map_target map_comp
      map_comp := map_comp }
  mapObjects_over := mapObjects_over
  mapArrows_over := mapArrows_over

/-- **An isomorphism of groupoids in algebraic spaces over a fixed base `B`.** A morphism each
way whose two composites are the identity, on the object space and on the arrow space.

`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom` is the notion of morphism, Stacks 043W
part (2); this is the matching notion of isomorphism, which the library did not have. It is
phrased as a pair of morphisms rather than as isomorphisms of the object and arrow spaces
carrying the structure, because `Hom` already packages compatibility with source, target and
composition, and because in that phrasing the identity law needs no clause at all — in each
direction `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mk'` supplies it. -/
structure Iso (G H : GroupoidInAlgebraicSpaces C S hS B) where
  /-- The morphism forwards. -/
  hom : Hom G H
  /-- The morphism backwards. -/
  inv : Hom H G
  /-- The two maps on object spaces are mutually inverse, one way round. -/
  mapObjects_hom_inv :
    hom.toGroupoidHom.mapObjects ≫ inv.toGroupoidHom.mapObjects = 𝟙 G.objects.obj
  /-- The two maps on object spaces are mutually inverse, the other way round. -/
  mapObjects_inv_hom :
    inv.toGroupoidHom.mapObjects ≫ hom.toGroupoidHom.mapObjects = 𝟙 H.objects.obj
  /-- The two maps on arrow spaces are mutually inverse, one way round. -/
  mapArrows_hom_inv :
    hom.toGroupoidHom.mapArrows ≫ inv.toGroupoidHom.mapArrows = 𝟙 G.arrows.obj
  /-- The two maps on arrow spaces are mutually inverse, the other way round. -/
  mapArrows_inv_hom :
    inv.toGroupoidHom.mapArrows ≫ hom.toGroupoidHom.mapArrows = 𝟙 H.arrows.obj

/-- An isomorphism of groupoids over `B` read in the other direction. -/
def Iso.symm {G H : GroupoidInAlgebraicSpaces C S hS B} (e : Iso G H) : Iso H G where
  hom := e.inv
  inv := e.hom
  mapObjects_hom_inv := e.mapObjects_inv_hom
  mapObjects_inv_hom := e.mapObjects_hom_inv
  mapArrows_hom_inv := e.mapArrows_inv_hom
  mapArrows_inv_hom := e.mapArrows_hom_inv

/-- **An isomorphism of groupoids over `B` out of a morphism whose two maps are invertible.**
The backwards morphism is not a hypothesis: a two-sided inverse of the map on object spaces and a
two-sided inverse of the map on arrow spaces are enough, because each of the four clauses of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom` for the backwards maps follows from the
corresponding clause for the forwards maps by cancelling the inverses — the composition clause by
injectivity of the forwards map on arrows, the identity clause not being a clause at all by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mk'`.

This is what makes a comparison of two constructions of a groupoid cost one `map_comp` rather
than two: `AlgebraicGeometry.Space.baseChangeCompIso` supplies only the forwards direction. -/
noncomputable def Iso.mk' {G H : GroupoidInAlgebraicSpaces C S hS B} (φ : Hom G H)
    (invObjects : H.objects.obj ⟶ G.objects.obj)
    (invArrows : H.arrows.obj ⟶ G.arrows.obj)
    (mapObjects_hom_inv : φ.toGroupoidHom.mapObjects ≫ invObjects = 𝟙 G.objects.obj)
    (mapObjects_inv_hom : invObjects ≫ φ.toGroupoidHom.mapObjects = 𝟙 H.objects.obj)
    (mapArrows_hom_inv : φ.toGroupoidHom.mapArrows ≫ invArrows = 𝟙 G.arrows.obj)
    (mapArrows_inv_hom : invArrows ≫ φ.toGroupoidHom.mapArrows = 𝟙 H.arrows.obj) :
    Iso G H := by
  have hmoPt : ∀ (T : (BigFppfOver C S hS)ᵒᵖ) (w : G.objects.obj.obj T),
      invObjects.app T (φ.toGroupoidHom.mapObjects.app T w) = w :=
    fun T w => congrArg (fun m => m.app T w) mapObjects_hom_inv
  have homPt : ∀ (T : (BigFppfOver C S hS)ᵒᵖ) (y : H.objects.obj.obj T),
      φ.toGroupoidHom.mapObjects.app T (invObjects.app T y) = y :=
    fun T y => congrArg (fun m => m.app T y) mapObjects_inv_hom
  have hamPt : ∀ (T : (BigFppfOver C S hS)ᵒᵖ) (y : H.arrows.obj.obj T),
      φ.toGroupoidHom.mapArrows.app T (invArrows.app T y) = y :=
    fun T y => congrArg (fun m => m.app T y) mapArrows_inv_hom
  have hmaPt : ∀ (T : (BigFppfOver C S hS)ᵒᵖ) (z : G.arrows.obj.obj T),
      invArrows.app T (φ.toGroupoidHom.mapArrows.app T z) = z :=
    fun T z => congrArg (fun m => m.app T z) mapArrows_hom_inv
  have hsinvPt : ∀ (T : (BigFppfOver C S hS)ᵒᵖ) (y : H.arrows.obj.obj T),
      G.source.hom.app T (invArrows.app T y) =
        invObjects.app T (H.source.hom.app T y) := by
    intro T y
    calc G.source.hom.app T (invArrows.app T y)
        = invObjects.app T (φ.toGroupoidHom.mapObjects.app T
            (G.source.hom.app T (invArrows.app T y))) := (hmoPt T _).symm
      _ = invObjects.app T (H.source.hom.app T
            (φ.toGroupoidHom.mapArrows.app T (invArrows.app T y))) :=
          congrArg (fun z => invObjects.app T z)
            (φ.toGroupoidHom.map_source T (invArrows.app T y)).symm
      _ = invObjects.app T (H.source.hom.app T y) :=
          congrArg (fun z => invObjects.app T (H.source.hom.app T z)) (hamPt T y)
  have htinvPt : ∀ (T : (BigFppfOver C S hS)ᵒᵖ) (y : H.arrows.obj.obj T),
      G.target.hom.app T (invArrows.app T y) =
        invObjects.app T (H.target.hom.app T y) := by
    intro T y
    calc G.target.hom.app T (invArrows.app T y)
        = invObjects.app T (φ.toGroupoidHom.mapObjects.app T
            (G.target.hom.app T (invArrows.app T y))) := (hmoPt T _).symm
      _ = invObjects.app T (H.target.hom.app T
            (φ.toGroupoidHom.mapArrows.app T (invArrows.app T y))) :=
          congrArg (fun z => invObjects.app T z)
            (φ.toGroupoidHom.map_target T (invArrows.app T y)).symm
      _ = invObjects.app T (H.target.hom.app T y) :=
          congrArg (fun z => invObjects.app T (H.target.hom.app T z)) (hamPt T y)
  have hbaseObjects : invObjects ≫ G.objectsToBase.hom = H.objectsToBase.hom := by
    ext T y
    exact (congrArg (fun m => m.app T (invObjects.app T y)) φ.mapObjects_over).symm.trans
      (congrArg (fun z => H.objectsToBase.hom.app T z) (homPt T y))
  have hbaseArrows : invArrows ≫ G.arrowsToBase.hom = H.arrowsToBase.hom := by
    ext T y
    exact (congrArg (fun m => m.app T (invArrows.app T y)) φ.mapArrows_over).symm.trans
      (congrArg (fun z => H.arrowsToBase.hom.app T z) (hamPt T y))
  have hinj : ∀ (T : (BigFppfOver C S hS)ᵒᵖ),
      Function.Injective (φ.toGroupoidHom.mapArrows.app T) := by
    intro T z₁ z₂ hz
    exact ((hmaPt T z₁).symm.trans (congrArg (fun z => invArrows.app T z) hz)).trans
      (hmaPt T z₂)
  have hcongr : ∀ (T : (BigFppfOver C S hS)ᵒᵖ) (x₁ x₂ y₁ y₂ : H.arrows.obj.obj T)
      (p : H.source.hom.app T x₁ = H.target.hom.app T y₁)
      (q : H.source.hom.app T x₂ = H.target.hom.app T y₂),
      x₁ = x₂ → y₁ = y₂ →
      H.toGroupoidInFunctors.compose T x₁ y₁ p =
        H.toGroupoidInFunctors.compose T x₂ y₂ q := by
    intro T x₁ x₂ y₁ y₂ p q ex ey
    subst ex
    subst ey
    rfl
  exact
    { hom := φ
      inv := Hom.mk' invObjects invArrows
        hsinvPt htinvPt
        (fun T x y hxy => by
          refine hinj T ?_
          refine ((φ.toGroupoidHom.map_comp T (invArrows.app T x)
            (invArrows.app T y) _).symm.trans ?_).trans (hamPt T _).symm
          exact hcongr T _ x _ y _ hxy (hamPt T x) (hamPt T y))
        hbaseObjects hbaseArrows
      mapObjects_hom_inv := mapObjects_hom_inv
      mapObjects_inv_hom := mapObjects_inv_hom
      mapArrows_hom_inv := mapArrows_hom_inv
      mapArrows_inv_hom := mapArrows_inv_hom }

/-- The map on object spaces underlying an isomorphism of groupoids is an isomorphism of
presheaves. -/
theorem Iso.isIso_mapObjects {G H : GroupoidInAlgebraicSpaces C S hS B} (e : Iso G H) :
    IsIso e.hom.toGroupoidHom.mapObjects :=
  ⟨e.inv.toGroupoidHom.mapObjects, e.mapObjects_hom_inv, e.mapObjects_inv_hom⟩

/-- The map on arrow spaces underlying an isomorphism of groupoids is an isomorphism of
presheaves. -/
theorem Iso.isIso_mapArrows {G H : GroupoidInAlgebraicSpaces C S hS B} (e : Iso G H) :
    IsIso e.hom.toGroupoidHom.mapArrows :=
  ⟨e.inv.toGroupoidHom.mapArrows, e.mapArrows_hom_inv, e.mapArrows_inv_hom⟩

end GroupoidInAlgebraicSpaces

namespace Space

/-! ### Composing two base changes: the comparison isomorphism

With the source, target and composition clauses in hand the comparison of the two base changes is
a morphism of groupoids over `B''` by `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mk'`, and
an isomorphism by `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Iso.mk'`, the inverse maps being
the inverse of `CategoryTheory.Limits.pullbackRightPullbackFstIso` on each of the two spaces.
-/

/-- **The morphism of groupoids over `B''` from the twice-base-changed groupoid to the base change
along the composite.** Its maps on objects and on arrows are the comparison
`CategoryTheory.Limits.pullbackRightPullbackFstIso` of iterated fibre products, which is already
the comparison of the object and of the arrow spaces on the nose. -/
noncomputable def baseChangeCompHom {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B B' B'' : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (h : B' ⟶ B) (k : B'' ⟶ B') :
    GroupoidInAlgebraicSpaces.Hom (baseChange (baseChange G h).groupoid k).groupoid
      (baseChange G (k ≫ h)).groupoid :=
  GroupoidInAlgebraicSpaces.Hom.mk'
    (pullbackRightPullbackFstIso h.hom G.objectsToBase.hom k.hom).hom
    (pullbackRightPullbackFstIso h.hom G.arrowsToBase.hom k.hom).hom
    (fun T a => congrArg (fun m => m.app T a)
      (pullbackRightPullbackFstIso_hom_comp_baseChange_source G h k))
    (fun T a => congrArg (fun m => m.app T a)
      (pullbackRightPullbackFstIso_hom_comp_baseChange_target G h k))
    (fun T a b hab => pullbackRightPullbackFstIso_hom_baseChange_map_comp G h k T a b hab _)
    (pullbackRightPullbackFstIso_hom_fst _ _ _)
    (pullbackRightPullbackFstIso_hom_fst _ _ _)

/-- **Base changing a groupoid in algebraic spaces twice is base changing it along the
composite.** An isomorphism of groupoids in algebraic spaces over `B''` between
`AlgebraicGeometry.Space.baseChange (AlgebraicGeometry.Space.baseChange G h) k` and
`AlgebraicGeometry.Space.baseChange G (k ≫ h)`, given by
`CategoryTheory.Limits.pullbackRightPullbackFstIso` on the object and on the arrow spaces.

Both object spaces are the same iterated fibre product and both arrow spaces are too, so there is
nothing to construct there; what the isomorphism carries is the groupoid structure, and the
content is `AlgebraicGeometry.Space.pullbackRightPullbackFstIso_hom_baseChange_map_comp`. -/
noncomputable def baseChangeCompIso {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B B' B'' : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (h : B' ⟶ B) (k : B'' ⟶ B') :
    GroupoidInAlgebraicSpaces.Iso
      (baseChange (baseChange G h).groupoid k).groupoid
      (baseChange G (k ≫ h)).groupoid :=
  GroupoidInAlgebraicSpaces.Iso.mk' (baseChangeCompHom G h k)
    (pullbackRightPullbackFstIso h.hom G.objectsToBase.hom k.hom).inv
    (pullbackRightPullbackFstIso h.hom G.arrowsToBase.hom k.hom).inv
    (pullbackRightPullbackFstIso h.hom G.objectsToBase.hom k.hom).hom_inv_id
    (pullbackRightPullbackFstIso h.hom G.objectsToBase.hom k.hom).inv_hom_id
    (pullbackRightPullbackFstIso h.hom G.arrowsToBase.hom k.hom).hom_inv_id
    (pullbackRightPullbackFstIso h.hom G.arrowsToBase.hom k.hom).inv_hom_id

end Space

end AlgebraicGeometry

end
