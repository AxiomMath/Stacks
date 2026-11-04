module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.Defs
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageTwoMorSheaf
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffineChart
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical

/-!
# Finite étale covers over the big fppf site of a scheme

Let `S` be a scheme contained in a big fppf site. The category `FÉt` has as objects the finite
étale morphisms `U ⟶ T` of the big fppf category over `S`, and as morphisms all commutative
squares; the functor `p : FÉt ⟶ (Sch/S)_fppf` sends such an object to its base `T`.

## Main definitions

* `AlgebraicGeometry.finiteEtaleHom`: being finite and étale on underlying schemes, as a
  morphism property of the big fppf category over `S`.
* `AlgebraicGeometry.FiniteEtaleCovers`: the category `FÉt`.
* `AlgebraicGeometry.finiteEtaleProjection`: the functor `p : FÉt ⟶ (Sch/S)_fppf`.
* `AlgebraicGeometry.FiniteEtaleCovers.baseChange` and
  `AlgebraicGeometry.FiniteEtaleCovers.baseChangeHom`: the base change of a finite étale cover
  along a morphism of the site, and the cartesian square exhibiting it as such.
* `AlgebraicGeometry.FiniteEtaleCovers.baseChangeLift`: a morphism into a base change, from a
  morphism to the total space and a morphism to the base.
* `AlgebraicGeometry.finiteEtaleFactorBaseChange`: the factorisation of a morphism of `FÉt`
  through the base change of its target along the morphism of bases it lies over.

## Main results

* `AlgebraicGeometry.finiteEtaleHom_isStableUnderBaseChange`: being finite étale on underlying
  schemes is stable under base change in the big fppf category over `S`.
* `AlgebraicGeometry.finiteEtaleProjection_isFibered`: `p` is a fibred category, condition (1)
  of Stacks 026F for `FÉt`.
* `AlgebraicGeometry.finiteEtaleProjection_eq_of_locallyEqual`: locally equal morphisms of
  `FÉt` are equal, the separatedness half of condition (2) of Stacks 026F for `FÉt`.

## Implementation notes

An object of `FÉt` is an arrow of the big fppf category over `S` whose underlying morphism of
schemes is finite and étale, so `FÉt` is `CategoryTheory.MorphismProperty.Arrow` at the inverse
image of `AlgebraicGeometry.IsFinite ⊓ AlgebraicGeometry.Etale` along the canonical functor to
schemes, with no condition on the two legs of a morphism; `p` is the target projection. The
fibred structure is the fibre product of the site, which the canonical functor to schemes
preserves, so the base change of a finite étale morphism is read off in schemes.

## References

* [Stacks Project, Tag 0BLY](https://stacks.math.columbia.edu/tag/0BLY)
* [Stacks Project, Tag 0BLZ](https://stacks.math.columbia.edu/tag/0BLZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being finite and étale on underlying schemes, as a morphism property of the big fppf
category over `S`. -/
@[ega "IV 18.10.9"]
def finiteEtaleHom : MorphismProperty (BigFppfOver B S hS) :=
  ((@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u})).inverseImage
    (BigFppfOver.toScheme B S hS)

/-- The category `FÉt` of Stacks 0BLY over a big fppf site: an object is a finite étale
morphism `U ⟶ T` of the big fppf category over `S`, and a morphism is a commutative square. -/
@[stacks 0BLY "the category FÉt of the section: objects are the finite étale morphisms of the
  big fppf category over S, morphisms are the commutative squares"]
abbrev FiniteEtaleCovers : Type _ :=
  MorphismProperty.Arrow (finiteEtaleHom B S hS) ⊤ ⊤

/-- The functor `p : FÉt ⟶ (Sch/S)_fppf` of Stacks 0BLY, sending a finite étale morphism
`U ⟶ T` to its base `T`. -/
@[stacks 0BLY "the functor p of the section, sending a finite étale cover to its base"]
def finiteEtaleProjection : FiniteEtaleCovers B S hS ⥤ BigFppfOver B S hS :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ Arrow.rightFunc

/-- The functor `finiteEtaleProjection` sends a finite étale cover to its base. -/
@[simp]
lemma finiteEtaleProjection_obj (a : FiniteEtaleCovers B S hS) :
    (finiteEtaleProjection B S hS).obj a = a.right := rfl

/-- The functor `finiteEtaleProjection` sends a commutative square to its morphism of bases. -/
@[simp]
lemma finiteEtaleProjection_map {a b : FiniteEtaleCovers B S hS} (φ : a ⟶ b) :
    (finiteEtaleProjection B S hS).map φ = φ.right := rfl

/-- Finite étale morphisms of the big fppf category over `S` are stable under base change:
the canonical functor to schemes preserves fibre products, and finiteness and étaleness of a
morphism of schemes are stable under base change. -/
instance finiteEtaleHom_isStableUnderBaseChange :
    (finiteEtaleHom B S hS).IsStableUnderBaseChange where
  of_isPullback sq hg := by
    have : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange :=
      MorphismProperty.IsStableUnderBaseChange.inf
    exact MorphismProperty.of_isPullback
      (P := (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}))
      (sq.map (BigFppfOver.toScheme B S hS)) hg

/-- A commutative square of finite étale covers lifts the morphism of bases it is built from. -/
lemma finiteEtaleProjection_isHomLift_homMk {x y : FiniteEtaleCovers B S hS}
    (l : x.left ⟶ y.left) (r : x.right ⟶ y.right) (w : l ≫ y.hom = x.hom ≫ r) :
    (finiteEtaleProjection B S hS).IsHomLift r (MorphismProperty.Arrow.homMk l r w) :=
  IsHomLift.map (finiteEtaleProjection B S hS) (MorphismProperty.Arrow.homMk l r w)

/-- **Condition (1) of Stacks 026F for `FÉt`.** The functor `p : FÉt ⟶ (Sch/S)_fppf` is a
fibred category: the strongly cartesian lift of a morphism `f : T ⟶ T'` with target the finite
étale cover `U ⟶ T'` is the base change `U ×_{T'} T ⟶ T`, again finite étale. -/
@[stacks 0BLZ "condition (1) of Stacks 026F: `p` is a fibred category. Condition (2), that the
  presheaves Mor(x, y) are fppf sheaves, is
  `AlgebraicGeometry.finiteEtaleProjection_isMorSheaf`."]
instance finiteEtaleProjection_isFibered :
    (finiteEtaleProjection B S hS).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro a T f
  have hb : finiteEtaleHom B S hS (pullback.snd a.hom f) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback a.hom f) a.prop
  refine ⟨MorphismProperty.Arrow.mk (pullback.snd a.hom f) hb,
    MorphismProperty.Arrow.homMk (pullback.fst a.hom f) f pullback.condition, ?_⟩
  have h₀ := finiteEtaleProjection_isHomLift_homMk B S hS
    (x := MorphismProperty.Arrow.mk (pullback.snd a.hom f) hb) (y := a)
    (pullback.fst a.hom f) f pullback.condition
  refine { toIsHomLift := h₀, universal_property' := ?_ }
  intro c g φ' hφ'
  have hr : g ≫ f = φ'.right :=
    IsHomLift.eq_of_isHomLift (finiteEtaleProjection B S hS) (g ≫ f) φ'
  have hw : φ'.left ≫ a.hom = (c.hom ≫ g) ≫ f :=
    ((MorphismProperty.Arrow.w φ').trans
      (congrArg (fun m => c.hom ≫ m) hr.symm)).trans (Category.assoc _ _ _).symm
  have hχ := finiteEtaleProjection_isHomLift_homMk B S hS (x := c)
    (y := MorphismProperty.Arrow.mk (pullback.snd a.hom f) hb)
    (pullback.lift φ'.left (c.hom ≫ g) hw) g (pullback.lift_snd _ _ hw)
  refine ⟨MorphismProperty.Arrow.homMk (pullback.lift φ'.left (c.hom ≫ g) hw) g
      (pullback.lift_snd _ _ hw),
    ⟨hχ, MorphismProperty.Arrow.Hom.ext (pullback.lift_fst _ _ hw) hr⟩, ?_⟩
  rintro ψ ⟨hψ, hψ'⟩
  have hψr : g = ψ.right :=
    @IsHomLift.eq_of_isHomLift _ _ _ _ (finiteEtaleProjection B S hS) _ _ g ψ hψ
  refine MorphismProperty.Arrow.Hom.ext ?_ hψr.symm
  refine pullback.hom_ext ?_ ?_
  · exact (congrArg (fun m => m.left) hψ').trans (pullback.lift_fst _ _ hw).symm
  · refine (MorphismProperty.Arrow.w ψ).trans ?_
    exact (congrArg (fun m => c.hom ≫ m) hψr.symm).trans (pullback.lift_snd _ _ hw).symm

/-! ### Base changes of a finite étale cover -/

/-- The base change of a finite étale cover `a` along a morphism `h : V ⟶ T` of the big fppf
category over `S`, as an object of `FÉt` with base `V`. -/
noncomputable def FiniteEtaleCovers.baseChange (a : FiniteEtaleCovers B S hS)
    {V : BigFppfOver B S hS} (h : V ⟶ a.right) : FiniteEtaleCovers B S hS :=
  MorphismProperty.Arrow.mk (pullback.snd a.hom h)
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback a.hom h) a.prop)

/-- The cartesian square exhibiting `FiniteEtaleCovers.baseChange a h` as a base change of `a`. -/
noncomputable def FiniteEtaleCovers.baseChangeHom (a : FiniteEtaleCovers B S hS)
    {V : BigFppfOver B S hS} (h : V ⟶ a.right) : FiniteEtaleCovers.baseChange B S hS a h ⟶ a :=
  MorphismProperty.Arrow.homMk (pullback.fst a.hom h) h pullback.condition

/-- The square `FiniteEtaleCovers.baseChangeHom a h` lies over `h`. -/
@[simp]
lemma FiniteEtaleCovers.baseChangeHom_right (a : FiniteEtaleCovers B S hS)
    {V : BigFppfOver B S hS} (h : V ⟶ a.right) :
    (FiniteEtaleCovers.baseChangeHom B S hS a h).right = h := rfl

/-- The morphism into a base change of `a` determined by a morphism `k` to the total space of
`a` and a morphism `m` to the base of `h`, agreeing over `a.right`. -/
noncomputable def FiniteEtaleCovers.baseChangeLift (a : FiniteEtaleCovers B S hS)
    {V W : BigFppfOver B S hS} (h : W ⟶ a.right) (k : V ⟶ a.left) (m : V ⟶ W)
    (hkm : k ≫ a.hom = m ≫ h) :
    V ⟶ (FiniteEtaleCovers.baseChange B S hS a h).left :=
  pullback.lift k m hkm

/-- The morphism `FiniteEtaleCovers.baseChangeLift a h k m hkm` followed by the projection to
the total space of `a` is `k`. -/
@[simp]
lemma FiniteEtaleCovers.baseChangeLift_comp_fst (a : FiniteEtaleCovers B S hS)
    {V W : BigFppfOver B S hS} (h : W ⟶ a.right) (k : V ⟶ a.left) (m : V ⟶ W)
    (hkm : k ≫ a.hom = m ≫ h) :
    FiniteEtaleCovers.baseChangeLift B S hS a h k m hkm ≫ pullback.fst a.hom h = k :=
  pullback.lift_fst _ _ _

/-- The morphism `FiniteEtaleCovers.baseChangeLift a h k m hkm` followed by the projection to
the base `W` is `m`. -/
@[simp]
lemma FiniteEtaleCovers.baseChangeLift_comp_snd (a : FiniteEtaleCovers B S hS)
    {V W : BigFppfOver B S hS} (h : W ⟶ a.right) (k : V ⟶ a.left) (m : V ⟶ W)
    (hkm : k ≫ a.hom = m ≫ h) :
    FiniteEtaleCovers.baseChangeLift B S hS a h k m hkm ≫ pullback.snd a.hom h = m :=
  pullback.lift_snd _ _ _

/-- A morphism of `FÉt` factors through the base change of its target along the morphism of
bases that it lies over. -/
noncomputable def finiteEtaleFactorBaseChange {x a : FiniteEtaleCovers B S hS} (Φ : x ⟶ a) :
    x ⟶ FiniteEtaleCovers.baseChange B S hS a Φ.right :=
  MorphismProperty.Arrow.homMk
    (FiniteEtaleCovers.baseChangeLift B S hS a Φ.right Φ.left x.hom (MorphismProperty.Arrow.w Φ))
    (𝟙 _)
    ((FiniteEtaleCovers.baseChangeLift_comp_snd B S hS a Φ.right Φ.left x.hom
      (MorphismProperty.Arrow.w Φ)).trans (Category.comp_id _).symm)

/-- The factorisation of `Φ` through the base change of its target recovers `Φ`. -/
lemma finiteEtaleFactorBaseChange_comp {x a : FiniteEtaleCovers B S hS} (Φ : x ⟶ a) :
    finiteEtaleFactorBaseChange B S hS Φ ≫ FiniteEtaleCovers.baseChangeHom B S hS a Φ.right = Φ :=
  MorphismProperty.Arrow.Hom.ext
    (FiniteEtaleCovers.baseChangeLift_comp_fst B S hS a Φ.right Φ.left x.hom
      (MorphismProperty.Arrow.w Φ))
    (Category.id_comp _)

/-! ### The separatedness half of condition (2) of Stacks 026F -/

/-- **The separatedness half of condition (2) of Stacks 026F for `FÉt`.** Two morphisms of
`FÉt` with the same morphism of bases which agree after composition with every morphism lying
over a covering sieve of that base are equal: the covering sieve pulls back to a covering sieve
of the total space of the source, and the fppf topology is subcanonical, so a morphism out of
the total space is determined by its restrictions along that sieve. -/
theorem finiteEtaleProjection_eq_of_locallyEqual {x a : FiniteEtaleCovers B S hS} {F G : x ⟶ a}
    (h : (finiteEtaleProjection B S hS).LocallyEqual (BigFppfOver.topology B S hS) F G) :
    F = G := by
  obtain ⟨hbase, R, hR, hloc⟩ := h
  refine MorphismProperty.Arrow.Hom.ext ?_ hbase
  have hRpb : Sieve.pullback x.hom R ∈ (BigFppfOver.topology B S hS) x.left :=
    (BigFppfOver.topology B S hS).pullback_stable _ hR
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).1
    (BigFppfOver.isSheaf_yoneda_obj B S hS a.left)
  refine ((hsh _ hRpb).isSeparatedFor).ext ?_
  intro V k hk
  have hmem : R.arrows
      ((finiteEtaleProjection B S hS).map
        (FiniteEtaleCovers.baseChangeHom B S hS x (k ≫ x.hom))) := hk
  have hl : pullback.fst x.hom (k ≫ x.hom) ≫ F.left
      = pullback.fst x.hom (k ≫ x.hom) ≫ G.left :=
    congrArg (fun m => m.left) (hloc (FiniteEtaleCovers.baseChangeHom B S hS x (k ≫ x.hom)) hmem)
  have hs : FiniteEtaleCovers.baseChangeLift B S hS x (k ≫ x.hom) k (𝟙 V)
      (Category.id_comp (k ≫ x.hom)).symm ≫ pullback.fst x.hom (k ≫ x.hom) = k :=
    FiniteEtaleCovers.baseChangeLift_comp_fst _ _ _ _ _ _ _ _
  show k ≫ F.left = k ≫ G.left
  refine ((congrArg (fun t => t ≫ F.left) hs).symm.trans (Category.assoc _ _ _)).trans ?_
  refine (congrArg (fun t => _ ≫ t) hl).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ G.left) hs)

end AlgebraicGeometry

end
