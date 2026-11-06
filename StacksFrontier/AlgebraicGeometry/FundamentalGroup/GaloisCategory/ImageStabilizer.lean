module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.InertiaDiagram
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.OpenSubgroups
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.MorphismMap

/-!
# The image of the étale fundamental group of a finite étale cover

Let `f : T ⟶ S` be a finite étale morphism of connected schemes and let `t` be a geometric point
of `T`, so that `t.map f` is a geometric point of `S`. The scheme `T` is itself a finite étale
cover of `S`, and `t` is a point of its geometric fibre at `t.map f`. This file identifies the
image of the induced homomorphism `π₁(T, t) ⟶ π₁(S, t ∘ f)` of
`AlgebraicGeometry.etaleFundamentalGroupMap` with the stabilizer of that point:

`range (π₁(T, t) ⟶ π₁(S, t ∘ f)) = Stab_{π₁(S, t ∘ f)} t`.

In particular the image is one of the open subgroups of
`AlgebraicGeometry.EtaleFundamentalGroup.IsOpenSubgroup`, which is what makes the monodromy of a
pullback `f⁻¹F` factor through the corresponding finite quotient.

Both inclusions are elementary consequences of naturality of the fibre functor, and no
Galois-category input is needed. For the inclusion of the image in the stabilizer, the point of
the fibre of `T ×_S T ⟶ T` at `t` determined by `t` is the image of the unique point of the fibre
of the terminal cover under the diagonal, so every natural automorphism of the fibre functor of
`T` fixes it. For the reverse inclusion, a natural automorphism `σ` of the fibre functor of `S`
fixing `t` restricts to one of the fibre functor of `T`: a finite étale cover `W ⟶ T` is finite
étale over `S` as well, the fibre of `W` at `t` is the part of its fibre at `t ∘ f` lying over
the chosen point of the fibre of `T`, and naturality of `σ` along `W ⟶ T` shows that `σ`
preserves that part. Pushing a cover of `T` forward along `f` and restricting a point of the
fibre back are inverse to each other on the nose, which is why the restricted automorphism is
sent to `σ` by `AlgebraicGeometry.etaleFundamentalGroupMap`.

## Main definitions

* `AlgebraicGeometry.finiteEtaleCompose` — composition with a finite étale morphism
  `f : T ⟶ S`, as a functor `FÉt_T ⥤ FÉt_S`.
* `AlgebraicGeometry.finiteEtaleOverSource` — the source of a finite étale morphism, as a finite
  étale cover of its target.
* `AlgebraicGeometry.finiteEtaleOverSourcePoint` — the geometric point `t` of `T`, read as a
  point of the fibre of `T ⟶ S` at `t.map f`.
* `AlgebraicGeometry.finiteEtaleComposeFiberInclusion` — the fibre of a cover of `T` at `t`,
  included in the fibre at `t.map f` of its pushforward to `S`.
* `AlgebraicGeometry.etaleFundamentalGroupOfStabilizer` — the natural automorphism of the fibre
  functor of `T` obtained by restricting one of the fibre functor of `S` that fixes the chosen
  point.

## Main results

* `AlgebraicGeometry.range_etaleFundamentalGroupMap_eq_stabilizer` — the image of
  `π₁(T, t) ⟶ π₁(S, t ∘ f)` is the stabilizer of the chosen point of the geometric fibre.
* `AlgebraicGeometry.isOpenSubgroup_range_etaleFundamentalGroupMap` — hence that image is an
  open subgroup in the sense of Stacks 03VE.

## Implementation notes

The pushforward functor is `CategoryTheory.MorphismProperty.Over.map`, which leaves the
underlying scheme of an object and of a morphism untouched and composes the structure morphism
with `f`; this is why `AlgebraicGeometry.finiteEtaleComposeFiberInclusion` is the identity on the
underlying morphism of schemes and why both halves of the main proof come down to naturality.

Base change uses the *chosen* pullback, which is only definitionally the pullback, so the
computations with `pullback.diagonal` are written in term mode, as in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.MorphismMap`.

The main statement is not registered against Tag 0BND: the Stacks project's statement there is
the equivalence of `FÉt_S` with the finite `π₁(S, s)`-sets and the functoriality of `π₁`, and the
identification of the image proved here is their standard companion rather than one of their
parts.

## References

* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
* [Stacks Project, Tag 03VE](https://stacks.math.columbia.edu/tag/03VE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {T S : Scheme.{u}} {f : T ⟶ S}

/-- Composition with a finite étale morphism `f : T ⟶ S`, as a functor `FÉt_T ⥤ FÉt_S`: a
scheme finite étale over `T` is finite étale over `S`. -/
def finiteEtaleCompose (hf : finiteEtale f) : FiniteEtaleOver T ⥤ FiniteEtaleOver S :=
  MorphismProperty.Over.map ⊤ hf

/-- The pushforward of `W` along `f` has the same underlying scheme as `W`. -/
@[simp]
theorem finiteEtaleCompose_obj_left (hf : finiteEtale f) (W : FiniteEtaleOver T) :
    ((finiteEtaleCompose hf).obj W).left = W.left :=
  rfl

/-- The structure morphism of the pushforward of `W` along `f` is `W.hom ≫ f`. -/
@[simp]
theorem finiteEtaleCompose_obj_hom (hf : finiteEtale f) (W : FiniteEtaleOver T) :
    ((finiteEtaleCompose hf).obj W).hom = W.hom ≫ f :=
  rfl

/-- The pushforward along `f` of a morphism `φ` of finite étale covers of `T` has the same
underlying morphism of schemes as `φ`. -/
@[simp]
theorem finiteEtaleCompose_map_left (hf : finiteEtale f) {W W' : FiniteEtaleOver T}
    (φ : W ⟶ W') : ((finiteEtaleCompose hf).map φ).left = φ.left :=
  rfl

/-- The source of a finite étale morphism `f : T ⟶ S`, as a finite étale cover of its target. -/
def finiteEtaleOverSource (hf : finiteEtale f) : FiniteEtaleOver S :=
  MorphismProperty.Over.mk ⊤ f hf

/-- The underlying scheme of `T`, as a finite étale cover of `S`, is `T`. -/
@[simp]
theorem finiteEtaleOverSource_left (hf : finiteEtale f) :
    (finiteEtaleOverSource hf).left = T :=
  rfl

/-- The structure morphism of `T`, as a finite étale cover of `S`, is `f`. -/
@[simp]
theorem finiteEtaleOverSource_hom (hf : finiteEtale f) : (finiteEtaleOverSource hf).hom = f :=
  rfl

/-- The structure morphism of a finite étale cover `W ⟶ T`, read as a morphism from the
pushforward of `W` to `T` in the category of finite étale covers of `S`. -/
def finiteEtaleOverSourceProj (hf : finiteEtale f) (W : FiniteEtaleOver T) :
    (finiteEtaleCompose hf).obj W ⟶ finiteEtaleOverSource hf :=
  MorphismProperty.Over.homMk W.hom rfl trivial

/-- The first projection of a base-changed cover, read as a morphism from the pushforward of
`V ×_S T` to `V` in the category of finite étale covers of `S`. -/
def finiteEtaleComposeBaseChangeProj (hf : finiteEtale f) (V : FiniteEtaleOver S) :
    (finiteEtaleCompose hf).obj ((finiteEtaleBaseChange f).obj V) ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom f)
    (pullback.condition (f := V.hom) (g := f)) trivial

/-- A geometric point `t` of `T`, read as a point of the geometric fibre at `t.map f` of the
finite étale cover `T ⟶ S`. -/
def finiteEtaleOverSourcePoint (hf : finiteEtale f) (t : GeometricPoint T) :
    (finiteEtaleFiberFunctor (t.map f)).obj (finiteEtaleOverSource hf) :=
  ⟨t.hom, rfl⟩

/-- A lift of `t` to a finite étale cover `W` of `T`, read as a lift of `t.map f` to the
pushforward of `W` to `S`; the underlying morphism of schemes is unchanged. -/
def finiteEtaleComposeFiberInclusion (hf : finiteEtale f) (t : GeometricPoint T)
    (W : FiniteEtaleOver T) (g : (finiteEtaleFiberFunctor t).obj W) :
    (finiteEtaleFiberFunctor (t.map f)).obj ((finiteEtaleCompose hf).obj W) :=
  ⟨g.1, by
    change g.1 ≫ W.hom ≫ f = t.hom ≫ f
    rw [← Category.assoc, g.2]⟩

/-- The geometric fibre of the terminal finite étale cover has at most one point: a lift of `t`
to `T` itself is `t`. -/
theorem subsingleton_finiteEtaleFiber_finiteEtaleOverTerminal (t : GeometricPoint T) :
    Subsingleton ((finiteEtaleFiberFunctor t).obj (finiteEtaleOverTerminal T)) := by
  refine ⟨fun a b ↦ Subtype.ext ?_⟩
  have ha : a.1 ≫ 𝟙 (finiteEtaleOverTerminal T).left = t.hom := a.2
  have hb : b.1 ≫ 𝟙 (finiteEtaleOverTerminal T).left = t.hom := b.2
  rw [Category.comp_id] at ha hb
  rw [ha, hb]

section Stabilizer

variable [ConnectedSpace S] (hf : finiteEtale f) (t : GeometricPoint T)

/-- A natural automorphism of a fibre functor commutes with the maps induced by morphisms of
covers. -/
private theorem app_map_apply {X : Scheme.{u}} [ConnectedSpace X] {x : GeometricPoint X}
    (σ : EtaleFundamentalGroup X x) {V W : FiniteEtaleOver X} (φ : V ⟶ W)
    (g : (finiteEtaleFiberFunctor x).obj V) :
    ConcreteCategory.hom (σ.asIso.hom.app W)
        (ConcreteCategory.hom ((finiteEtaleFiberFunctor x).map φ) g)
      = ConcreteCategory.hom ((finiteEtaleFiberFunctor x).map φ)
          (ConcreteCategory.hom (σ.asIso.hom.app V) g) :=
  NatTrans.naturality_apply σ.asIso.hom φ g

/-- **The stabilizer of the chosen point preserves the fibres over `T`.** If a natural
automorphism `σ` of the fibre functor at `t.map f` fixes the point of the fibre of `T ⟶ S` given
by `t`, then for every finite étale cover `W ⟶ T` it carries a lift of `t` to `W` again to a
lift of `t`. -/
theorem comp_finiteEtaleComposeFiberInclusion_of_mem_stabilizer
    (σ : EtaleFundamentalGroup S (t.map f))
    (hσ : σ • finiteEtaleOverSourcePoint hf t = finiteEtaleOverSourcePoint hf t)
    (W : FiniteEtaleOver T) (g : (finiteEtaleFiberFunctor t).obj W) :
    ((σ.asIso.app ((finiteEtaleCompose hf).obj W)).hom
        (finiteEtaleComposeFiberInclusion hf t W g)).1 ≫ W.hom = t.hom := by
  have hσ' : ConcreteCategory.hom (σ.asIso.hom.app (finiteEtaleOverSource hf))
      (finiteEtaleOverSourcePoint hf t) = finiteEtaleOverSourcePoint hf t := hσ
  have h := app_map_apply σ (finiteEtaleOverSourceProj hf W)
    (finiteEtaleComposeFiberInclusion hf t W g)
  have hpt : ConcreteCategory.hom ((finiteEtaleFiberFunctor (t.map f)).map
        (finiteEtaleOverSourceProj hf W)) (finiteEtaleComposeFiberInclusion hf t W g)
      = finiteEtaleOverSourcePoint hf t := Subtype.ext g.2
  rw [hpt, hσ'] at h
  exact (congrArg Subtype.val h).symm

/-- The action on the fibre at `t` of a cover of `T` of an element of the stabilizer of the
chosen point: restrict the action on the fibre at `t.map f` of the pushforward. -/
def finiteEtaleFiberRestrict
    (σ : MulAction.stabilizer (EtaleFundamentalGroup S (t.map f))
      (finiteEtaleOverSourcePoint hf t))
    (W : FiniteEtaleOver T) (g : (finiteEtaleFiberFunctor t).obj W) :
    (finiteEtaleFiberFunctor t).obj W :=
  ⟨(((σ : EtaleFundamentalGroup S (t.map f)).asIso.app ((finiteEtaleCompose hf).obj W)).hom
      (finiteEtaleComposeFiberInclusion hf t W g)).1,
    comp_finiteEtaleComposeFiberInclusion_of_mem_stabilizer hf t _ σ.2 W g⟩

/-- The restricted actions of an element of the stabilizer and of its inverse are inverse. -/
theorem finiteEtaleFiberRestrict_inv_finiteEtaleFiberRestrict
    (σ : MulAction.stabilizer (EtaleFundamentalGroup S (t.map f))
      (finiteEtaleOverSourcePoint hf t))
    (W : FiniteEtaleOver T) (g : (finiteEtaleFiberFunctor t).obj W) :
    finiteEtaleFiberRestrict hf t σ⁻¹ W (finiteEtaleFiberRestrict hf t σ W g) = g := by
  refine Subtype.ext ?_
  have hinc : finiteEtaleComposeFiberInclusion hf t W (finiteEtaleFiberRestrict hf t σ W g)
      = ((σ : EtaleFundamentalGroup S (t.map f)).asIso.app ((finiteEtaleCompose hf).obj W)).hom
          (finiteEtaleComposeFiberInclusion hf t W g) := Subtype.ext rfl
  show (((σ⁻¹ : EtaleFundamentalGroup S (t.map f)).asIso.app
      ((finiteEtaleCompose hf).obj W)).hom
      (finiteEtaleComposeFiberInclusion hf t W (finiteEtaleFiberRestrict hf t σ W g))).1 = g.1
  rw [hinc]
  have hinv : ((σ⁻¹ : EtaleFundamentalGroup S (t.map f)).asIso.app
      ((finiteEtaleCompose hf).obj W)).hom
      (((σ : EtaleFundamentalGroup S (t.map f)).asIso.app
        ((finiteEtaleCompose hf).obj W)).hom
        (finiteEtaleComposeFiberInclusion hf t W g))
      = finiteEtaleComposeFiberInclusion hf t W g :=
    ((σ : EtaleFundamentalGroup S (t.map f)).asIso.app
      ((finiteEtaleCompose hf).obj W)).hom_inv_id_apply _
  rw [hinv]
  rfl

/-- The restricted action is natural in the finite étale cover of `T`. -/
theorem finiteEtaleFiberRestrict_naturality
    (σ : MulAction.stabilizer (EtaleFundamentalGroup S (t.map f))
      (finiteEtaleOverSourcePoint hf t))
    {W W' : FiniteEtaleOver T} (φ : W ⟶ W') (g : (finiteEtaleFiberFunctor t).obj W) :
    finiteEtaleFiberRestrict hf t σ W' ((finiteEtaleFiberFunctor t).map φ g)
      = (finiteEtaleFiberFunctor t).map φ (finiteEtaleFiberRestrict hf t σ W g) := by
  have h := app_map_apply (σ : EtaleFundamentalGroup S (t.map f)) ((finiteEtaleCompose hf).map φ)
    (finiteEtaleComposeFiberInclusion hf t W g)
  have hL : ConcreteCategory.hom ((finiteEtaleFiberFunctor (t.map f)).map
        ((finiteEtaleCompose hf).map φ)) (finiteEtaleComposeFiberInclusion hf t W g)
      = finiteEtaleComposeFiberInclusion hf t W'
        ((finiteEtaleFiberFunctor t).map φ g) := Subtype.ext rfl
  rw [hL] at h
  refine Subtype.ext ?_
  have h2 : (((σ : EtaleFundamentalGroup S (t.map f)).asIso.app
        ((finiteEtaleCompose hf).obj W')).hom
        (finiteEtaleComposeFiberInclusion hf t W'
          ((finiteEtaleFiberFunctor t).map φ g))).1
      = (((σ : EtaleFundamentalGroup S (t.map f)).asIso.app
          ((finiteEtaleCompose hf).obj W)).hom
          (finiteEtaleComposeFiberInclusion hf t W g)).1 ≫ φ.left :=
    congrArg Subtype.val h
  exact h2

/-- The restricted action of an element of the stabilizer, as a bijection of the fibre. -/
def finiteEtaleFiberRestrictEquiv
    (σ : MulAction.stabilizer (EtaleFundamentalGroup S (t.map f))
      (finiteEtaleOverSourcePoint hf t)) (W : FiniteEtaleOver T) :
    (finiteEtaleFiberFunctor t).obj W ≃ (finiteEtaleFiberFunctor t).obj W where
  toFun := finiteEtaleFiberRestrict hf t σ W
  invFun := finiteEtaleFiberRestrict hf t σ⁻¹ W
  left_inv := finiteEtaleFiberRestrict_inv_finiteEtaleFiberRestrict hf t σ W
  right_inv g := by
    simpa using finiteEtaleFiberRestrict_inv_finiteEtaleFiberRestrict hf t σ⁻¹ W g

variable [ConnectedSpace T]

/-- **An element of `π₁(S, t ∘ f)` stabilizing the chosen point comes from `π₁(T, t)`.** The
restricted actions on the fibres of the finite étale covers of `T` assemble into a natural
automorphism of the fibre functor at `t`. -/
def etaleFundamentalGroupOfStabilizer
    (σ : MulAction.stabilizer (EtaleFundamentalGroup S (t.map f))
      (finiteEtaleOverSourcePoint hf t)) :
    EtaleFundamentalGroup T t :=
  Aut.of <| NatIso.ofComponents (fun W ↦ Equiv.toIso (finiteEtaleFiberRestrictEquiv hf t σ W))
    (fun φ ↦ by
      ext g
      exact finiteEtaleFiberRestrict_naturality hf t σ φ g)

omit [ConnectedSpace S] in
/-- Every natural automorphism of the fibre functor at `t` fixes the point of the fibre of
`T ×_S T ⟶ T` determined by `t`, because that point is the image of the unique point of the fibre
of the terminal cover under the diagonal of `f`. -/
theorem app_symm_finiteEtaleFiberProjectionEquiv_finiteEtaleOverSourcePoint
    (τ : EtaleFundamentalGroup T t) :
    (τ.asIso.app ((finiteEtaleBaseChange f).obj (finiteEtaleOverSource hf))).hom
        ((finiteEtaleFiberProjectionEquiv f t (finiteEtaleOverSource hf)).symm
          (finiteEtaleOverSourcePoint hf t))
      = (finiteEtaleFiberProjectionEquiv f t (finiteEtaleOverSource hf)).symm
          (finiteEtaleOverSourcePoint hf t) := by
  let u : (finiteEtaleFiberFunctor t).obj (finiteEtaleOverTerminal T) :=
    ⟨t.hom, Category.comp_id _⟩
  let Δ : finiteEtaleOverTerminal T ⟶
      (finiteEtaleBaseChange f).obj (finiteEtaleOverSource hf) :=
    MorphismProperty.Over.homMk (pullback.diagonal f)
      (show pullback.diagonal f ≫ pullback.snd f f = 𝟙 T from pullback.diagonal_snd f) trivial
  have hp : (finiteEtaleFiberProjectionEquiv f t (finiteEtaleOverSource hf)).symm
      (finiteEtaleOverSourcePoint hf t)
      = ConcreteCategory.hom ((finiteEtaleFiberFunctor t).map Δ) u := by
    have hcomp {k : pullback f f ⟶ T} (hk : pullback.diagonal f ≫ k = 𝟙 T) :
        (t.hom ≫ pullback.diagonal f) ≫ k = t.hom := by
      rw [Category.assoc, hk, Category.comp_id]
    exact Subtype.ext (pullback.hom_ext
      ((pullback.lift_fst _ _ _).trans (hcomp (pullback.diagonal_fst f)).symm)
      ((pullback.lift_snd _ _ _).trans (hcomp (pullback.diagonal_snd f)).symm))
  have hnat := app_map_apply τ Δ u
  rw [hp]
  rw [show ConcreteCategory.hom (τ.asIso.hom.app (finiteEtaleOverTerminal T)) u = u from
    (subsingleton_finiteEtaleFiber_finiteEtaleOverTerminal t).allEq _ _] at hnat
  exact hnat

/-- The restricted automorphism of the fibre functor at `t` is sent back to `σ` by the induced
homomorphism, computed on a single cover of `S`. -/
theorem etaleFundamentalGroupMap_etaleFundamentalGroupOfStabilizer_apply
    (σ : MulAction.stabilizer (EtaleFundamentalGroup S (t.map f))
      (finiteEtaleOverSourcePoint hf t))
    (V : FiniteEtaleOver S)
    (p : (finiteEtaleFiberFunctor t).obj ((finiteEtaleBaseChange f).obj V)) :
    finiteEtaleFiberProjection f t V
        (((etaleFundamentalGroupOfStabilizer hf t σ).asIso.app
          ((finiteEtaleBaseChange f).obj V)).hom p)
      = ConcreteCategory.hom
          ((finiteEtaleFiberFunctor (t.map f)).map (finiteEtaleComposeBaseChangeProj hf V))
          (ConcreteCategory.hom ((σ : EtaleFundamentalGroup S (t.map f)).asIso.hom.app
              ((finiteEtaleCompose hf).obj ((finiteEtaleBaseChange f).obj V)))
            (finiteEtaleComposeFiberInclusion hf t ((finiteEtaleBaseChange f).obj V) p)) :=
  Subtype.ext rfl

/-- **The image of `π₁(T, t) ⟶ π₁(S, t ∘ f)` is a fibre stabilizer.** For a finite étale
morphism `f : T ⟶ S` of connected schemes and a geometric point `t` of `T`, the image of the
induced homomorphism of étale fundamental groups is the stabilizer, for the action of
`π₁(S, t ∘ f)` on the geometric fibre of the cover `T ⟶ S`, of the point of that fibre given by
`t` itself. -/
theorem range_etaleFundamentalGroupMap_eq_stabilizer :
    (etaleFundamentalGroupMap f t).toMonoidHom.range
      = MulAction.stabilizer (EtaleFundamentalGroup S (t.map f))
          (finiteEtaleOverSourcePoint hf t) := by
  ext σ
  simp only [MonoidHom.mem_range, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨τ, rfl⟩
    have hmain := etaleFundamentalGroupMap_finiteEtaleFiberProjection f t
      (finiteEtaleOverSource hf) τ
      ((finiteEtaleFiberProjectionEquiv f t (finiteEtaleOverSource hf)).symm
        (finiteEtaleOverSourcePoint hf t))
    rw [app_symm_finiteEtaleFiberProjectionEquiv_finiteEtaleOverSourcePoint hf t τ] at hmain
    have hq : finiteEtaleFiberProjection f t (finiteEtaleOverSource hf)
        ((finiteEtaleFiberProjectionEquiv f t (finiteEtaleOverSource hf)).symm
          (finiteEtaleOverSourcePoint hf t)) = finiteEtaleOverSourcePoint hf t :=
      (finiteEtaleFiberProjectionEquiv f t (finiteEtaleOverSource hf)).apply_symm_apply _
    rw [hq] at hmain
    exact hmain.symm
  · intro hσ
    refine ⟨etaleFundamentalGroupOfStabilizer hf t ⟨σ, hσ⟩, CategoryTheory.Aut.ext ?_⟩
    ext V q
    have hnat := app_map_apply σ (finiteEtaleComposeBaseChangeProj hf V)
      (finiteEtaleComposeFiberInclusion hf t ((finiteEtaleBaseChange f).obj V)
        ((finiteEtaleFiberProjectionEquiv f t V).symm q))
    have hL : ConcreteCategory.hom ((finiteEtaleFiberFunctor (t.map f)).map
          (finiteEtaleComposeBaseChangeProj hf V))
        (finiteEtaleComposeFiberInclusion hf t ((finiteEtaleBaseChange f).obj V)
          ((finiteEtaleFiberProjectionEquiv f t V).symm q)) = q :=
      Subtype.ext (congrArg Subtype.val
        ((finiteEtaleFiberProjectionEquiv f t V).apply_symm_apply q))
    rw [hL] at hnat
    exact (etaleFundamentalGroupMap_etaleFundamentalGroupOfStabilizer_apply hf t ⟨σ, hσ⟩ V
      ((finiteEtaleFiberProjectionEquiv f t V).symm q)).trans hnat.symm

include hf in
/-- **The image of `π₁(T, t) ⟶ π₁(S, t ∘ f)` is an open subgroup**, in the sense of Stacks 03VE:
it is the stabilizer of a point of the geometric fibre of the finite étale cover `T ⟶ S`. -/
theorem isOpenSubgroup_range_etaleFundamentalGroupMap :
    EtaleFundamentalGroup.IsOpenSubgroup (t.map f)
      (etaleFundamentalGroupMap f t).toMonoidHom.range :=
  ⟨finiteEtaleOverSource hf, finiteEtaleOverSourcePoint hf t,
    range_etaleFundamentalGroupMap_eq_stabilizer hf t⟩

end Stabilizer

end AlgebraicGeometry

end
