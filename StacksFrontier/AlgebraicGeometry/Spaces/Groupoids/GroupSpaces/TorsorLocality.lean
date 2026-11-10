module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.ModObj
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PseudoTorsors
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings

/-!
# Base change and fppf locality of the torsor conditions

Let `G` be a group algebraic space over an algebraic space `B` acting on an algebraic space
`X` over `B`. The conditions of Stacks 04TW and Stacks 04TY on that action — being a
pseudo-torsor, and being trivialized by a covering family of the base — are stable under base
change, and both may be checked after an fppf covering of `B`.

## Main definitions

* `AlgebraicGeometry.Space.restrictGrpObj` and `AlgebraicGeometry.Space.restrictModObj` are
  the group law and the action carried to the restrictions of `G` and `X` along a morphism
  `B' ⟶ B`.
* `AlgebraicGeometry.Space.pullbackHomEquiv` identifies the points of the restriction of `X`
  along `b : B' ⟶ B` over a test object of the slice over `B'` with the points of `X` over the
  composite with `b`.

## Main results

* `AlgebraicGeometry.Space.isPseudoTorsor_restrict`: base change of the pseudo-torsor
  condition.
* `AlgebraicGeometry.Space.isTorsorFor_restrict` and
  `AlgebraicGeometry.Space.isFppfTorsor_restrict`: base change of local triviality, the second
  being the fppf case of the first.
* `AlgebraicGeometry.Space.nonempty_unitHom_pullback_iff`: a local section of `X` over `B'` is
  a factorization of `B' ⟶ B` through `X`.
* `AlgebraicGeometry.Space.isFppfTorsor_of_restrict`: a pseudo-torsor whose restriction to
  every member of an fppf covering of the base is an fppf torsor is an fppf torsor.
* `AlgebraicGeometry.Space.pullbackHomEquiv_smul`: the identification of the points of a
  restriction is equivariant.
* `AlgebraicGeometry.Space.isPseudoTorsor_of_forall_exists_lift` and
  `AlgebraicGeometry.Space.isFppfTorsor_of_forall_exists_lift`: locality of the two conditions
  along a family of morphisms to the base through which every section of the base factors.
* `AlgebraicGeometry.Space.exists_sieve_lift_of_isFppfCovering`: a section of the base over a
  test object of the big fppf site factors through a member of an fppf covering family of the
  base after passing to a covering sieve of the test object.
* `AlgebraicGeometry.Space.isPseudoTorsor_of_isFppfCovering` and
  `AlgebraicGeometry.Space.isFppfTorsor_of_isFppfCovering`: fppf locality of the two
  conditions along an fppf covering of the base.

## Implementation notes

A group algebraic space over `B` is a group object of the slice of presheaves over `B`, so its
restriction along `b : B' ⟶ B` is its image under `CategoryTheory.Over.pullback b`, which
preserves finite products. `CategoryTheory.Functor.mapGrp` carries the group law and
`CategoryTheory.Functor.LaxMonoidal.modObj` carries the action; both are instances.

## References

* [Stacks Project, Tag 04TW](https://stacks.math.columbia.edu/tag/04TW)
* [Stacks Project, Tag 04TY](https://stacks.math.columbia.edu/tag/04TY)
* [Stacks Project, Tag 03Y9](https://stacks.math.columbia.edu/tag/03Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory CategoryTheory.MonObj

universe u v w

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B B' : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

/-! ### Restricting a group object and an action along a morphism of the base -/

/-- The group-object structure on the restriction of a group object along a morphism of the
base, carried by the finite-product-preserving pullback functor. -/
instance restrictGrpObj (b : B' ⟶ B) (G : Over B) [GrpObj G] :
    GrpObj ((Over.pullback b).obj G) :=
  ((Over.pullback b).mapGrp.obj (.mk G)).grp

/-- The restriction of an action along a morphism of the base, as an action of the restricted
group object on the restricted object. -/
instance restrictModObj (b : B' ⟶ B) (G X : Over B) [GrpObj G] [ModObj G X] :
    ModObj ((Over.pullback b).obj G) ((Over.pullback b).obj X) :=
  Functor.LaxMonoidal.modObj (Over.pullback b) (restrictGrpObj b G).toMonObj rfl rfl

/-- The restriction of a pseudo-torsor along a morphism of the base is a pseudo-torsor under the
restricted group object. -/
theorem isPseudoTorsor_restrict (b : B' ⟶ B) (G X : Over B) [GrpObj G] [ModObj G X]
    (h : IsPseudoTorsor G X) :
    IsPseudoTorsor ((Over.pullback b).obj G) ((Over.pullback b).obj X) := by
  have : IsIso (ModObj.leftSMul G X) := h
  change IsIso (ModObj.leftSMul ((Over.pullback b).obj G) ((Over.pullback b).obj X))
  rw [Functor.LaxMonoidal.mapModObj_leftSMul (Over.pullback b) (X := X)
    (restrictGrpObj b G).toMonObj rfl rfl]
  infer_instance

/-- The action of the restriction of a group object on the restriction of an object it acts on
is the image of the original action, precomposed with the product comparison. -/
theorem restrictModObj_smul (b : B' ⟶ B) (G X : Over B) [GrpObj G] [ModObj G X] :
    γ[(Over.pullback b).obj G, (Over.pullback b).obj X] =
      Functor.LaxMonoidal.μ (Over.pullback b) G X ≫ (Over.pullback b).map γ[G, X] :=
  rfl

/-! ### Points of a restriction -/

/-- The points of the restriction of `X : Over B` along `b : B' ⟶ B` over a test object of the
slice over `B'`, presented by a morphism `z : Z ⟶ B'`, are the points of `X` over the
composite `z ≫ b`. -/
def pullbackHomEquiv (b : B' ⟶ B) (X : Over B)
    {Z : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (z : Z ⟶ B') :
    ((Over.mk z : Over B') ⟶ (Over.pullback b).obj X) ≃
      ((Over.mk (z ≫ b) : Over B) ⟶ X) where
  toFun u := Over.homMk (u.left ≫ pullback.fst X.hom b) (by
    have hu : u.left ≫ pullback.snd X.hom b = z := by simpa using u.w
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu]
    rfl)
  invFun x := Over.homMk (pullback.lift x.left z (by simp)) (pullback.lift_snd _ _ _)
  left_inv u := by
    apply Over.OverMorphism.ext
    refine pullback.hom_ext (pullback.lift_fst _ _ _) ?_
    exact (pullback.lift_snd _ _ _).trans u.w.symm
  right_inv x := Over.OverMorphism.ext (pullback.lift_fst _ _ _)

/-- `AlgebraicGeometry.Space.pullbackHomEquiv` composes a point of the restriction with the
projection to the original object. -/
@[simp]
theorem pullbackHomEquiv_apply_left (b : B' ⟶ B) (X : Over B)
    {Z : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (z : Z ⟶ B')
    (u : (Over.mk z : Over B') ⟶ (Over.pullback b).obj X) :
    (pullbackHomEquiv b X z u).left = u.left ≫ pullback.fst X.hom b :=
  rfl

/-- `AlgebraicGeometry.Space.pullbackHomEquiv` is equivariant: it carries the restricted action
on the points of a restriction to the original action on the points of the original object. -/
theorem pullbackHomEquiv_smul (b : B' ⟶ B) (G X : Over B) [GrpObj G] [ModObj G X]
    {Z : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (z : Z ⟶ B')
    (g : (Over.mk z : Over B') ⟶ (Over.pullback b).obj G)
    (u : (Over.mk z : Over B') ⟶ (Over.pullback b).obj X) :
    pullbackHomEquiv b X z (g • u) =
      pullbackHomEquiv b G z g • pullbackHomEquiv b X z u := by
  apply Over.OverMorphism.ext
  change (CartesianMonoidalCategory.lift g u ≫
      γ[(Over.pullback b).obj G, (Over.pullback b).obj X]).left ≫
      pullback.fst X.hom b =
    (CartesianMonoidalCategory.lift (pullbackHomEquiv b G z g)
      (pullbackHomEquiv b X z u) ≫ γ[G, X]).left
  rw [restrictModObj_smul]
  have key : (CartesianMonoidalCategory.lift g u).left ≫
      (Functor.LaxMonoidal.μ (Over.pullback b) G X).left ≫
        pullback.fst (G ⊗ X).hom b =
      (CartesianMonoidalCategory.lift (pullbackHomEquiv b G z g)
        (pullbackHomEquiv b X z u)).left := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [Over.μ_pullback_left_fst_fst]
      simp only [Over.lift_left, ← Category.assoc, pullback.lift_fst,
        pullbackHomEquiv_apply_left]
    · simp only [Category.assoc]
      rw [Over.μ_pullback_left_fst_snd]
      simp only [Over.lift_left, ← Category.assoc, pullback.lift_snd,
        pullbackHomEquiv_apply_left]
  simp only [Over.comp_left, Category.assoc]
  rw [show ((Over.pullback b).map γ[G, X]).left ≫ pullback.fst X.hom b =
      pullback.fst (G ⊗ X).hom b ≫ (γ[G, X]).left from pullback.lift_fst _ _ _]
  simpa only [Category.assoc] using congrArg (fun t => t ≫ (γ[G, X]).left) key

/-! ### Local sections -/

/-- A section of the restriction of `X : Over B` along `b : B' ⟶ B`, that is a morphism from
the monoidal unit of the slice over `B'`, is the same thing as a factorization of `b` through
the structure morphism of `X`. -/
theorem nonempty_unitHom_pullback_iff (b : B' ⟶ B) (X : Over B) :
    Nonempty (𝟙_ (Over B') ⟶ (Over.pullback b).obj X) ↔
      ∃ t : B' ⟶ X.left, t ≫ X.hom = b := by
  constructor
  · rintro ⟨s⟩
    have hs : s.left ≫ pullback.snd X.hom b = 𝟙 B' := by
      simpa using s.w
    refine ⟨s.left ≫ pullback.fst X.hom b, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · rintro ⟨t, ht⟩
    refine ⟨Over.homMk (pullback.lift t (𝟙 B') (by rw [ht]; simp)) ?_⟩
    change pullback.lift t (𝟙 B') _ ≫ pullback.snd X.hom b = 𝟙 B'
    exact pullback.lift_snd _ _ _

/-! ### Base change of local triviality -/

variable (𝒞 S hS) in
/-- If `X` is a pseudo-torsor under `G` over `B` trivialized by a family satisfying `P`, then
its restriction along `b : B' ⟶ B` is a pseudo-torsor under the
restricted group trivialized by the family of fibre products, provided that family satisfies
the covering property `P'` imposed over `B'`. -/
theorem isTorsorFor_restrict (hB : IsAlgebraicSpace 𝒞 S hS B)
    (hB' : IsAlgebraicSpace 𝒞 S hS B') (b : B' ⟶ B) (G X : Over B) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace 𝒞 S hS G.left) (hX : IsAlgebraicSpace 𝒞 S hS X.left)
    (P : ∀ (I : Type (u + 1)) (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u),
      (∀ i, Bᵢ i ⟶ B) → Prop)
    (P' : ∀ (I : Type (u + 1)) (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u),
      (∀ i, Bᵢ i ⟶ B') → Prop)
    (hPP' : ∀ (I : Type (u + 1)) (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
      (f : ∀ i, Bᵢ i ⟶ B), (∀ i, IsAlgebraicSpace 𝒞 S hS (Bᵢ i)) → P I Bᵢ f →
      P' I (fun i => pullback b (f i)) (fun i => pullback.fst b (f i)))
    (h : IsTorsorFor 𝒞 S hS B hB G X hG hX P) :
    IsTorsorFor 𝒞 S hS B' hB' ((Over.pullback b).obj G) ((Over.pullback b).obj X)
      (isAlgebraicSpace_pullback 𝒞 S hS G.hom b hG hB' hB)
      (isAlgebraicSpace_pullback 𝒞 S hS X.hom b hX hB' hB) P' := by
  obtain ⟨hp, I, Bᵢ, f, hBᵢ, hP, hsec⟩ := h
  refine ⟨isPseudoTorsor_restrict b G X hp, I, fun i => pullback b (f i),
    fun i => pullback.fst b (f i),
    fun i => isAlgebraicSpace_pullback 𝒞 S hS b (f i) hB' (hBᵢ i) hB,
    hPP' I Bᵢ f hBᵢ hP, fun i => ?_⟩
  obtain ⟨t, ht⟩ := (nonempty_unitHom_pullback_iff (f i) X).1 (hsec i)
  refine (nonempty_unitHom_pullback_iff (pullback.fst b (f i))
    ((Over.pullback b).obj X)).2 ⟨pullback.lift (pullback.snd b (f i) ≫ t)
      (pullback.fst b (f i)) ?_, ?_⟩
  · rw [Category.assoc, ht, ← pullback.condition]
  · exact pullback.lift_snd _ _ _

variable (𝒞 S hS) in
/-- The restriction of an fppf torsor along a morphism of algebraic spaces is an fppf
torsor. -/
theorem isFppfTorsor_restrict (hB : IsAlgebraicSpace 𝒞 S hS B)
    (hB' : IsAlgebraicSpace 𝒞 S hS B') (b : B' ⟶ B) (G X : Over B) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace 𝒞 S hS G.left) (hX : IsAlgebraicSpace 𝒞 S hS X.left)
    (h : IsFppfTorsor 𝒞 S hS B hB G X hG hX) :
    IsFppfTorsor 𝒞 S hS B' hB' ((Over.pullback b).obj G) ((Over.pullback b).obj X)
      (isAlgebraicSpace_pullback 𝒞 S hS G.hom b hG hB' hB)
      (isAlgebraicSpace_pullback 𝒞 S hS X.hom b hX hB' hB) := by
  refine isTorsorFor_restrict 𝒞 S hS hB hB' b G X hG hX _ _ (fun I Bᵢ f hBᵢ hcov => ?_) h
  exact isFppfCovering_fibreProduct 𝒞 S hS
    (X := (⟨B, hB⟩ : AlgebraicSpaces 𝒞 S hS))
    (X' := (⟨B', hB'⟩ : AlgebraicSpaces 𝒞 S hS))
    (fun i => (⟨Bᵢ i, hBᵢ i⟩ : AlgebraicSpaces 𝒞 S hS))
    (fun i => ObjectProperty.homMk (f i)) (ObjectProperty.homMk b) hcov

/-! ### Composing the trivializing coverings -/

variable (𝒞 S hS) in
/-- A pseudo-torsor whose restriction to every member of an fppf covering of the base is an fppf
torsor is itself an fppf torsor. -/
theorem isFppfTorsor_of_restrict (hB : IsAlgebraicSpace 𝒞 S hS B) (G X : Over B) [GrpObj G]
    [ModObj G X] (hG : IsAlgebraicSpace 𝒞 S hS G.left)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (hp : IsPseudoTorsor G X)
    {I : Type (u + 1)} (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, Bᵢ i ⟶ B)
    (hBᵢ : ∀ i, IsAlgebraicSpace 𝒞 S hS (Bᵢ i)) (hcov : IsFppfCovering 𝒞 S hS Bᵢ f)
    (htriv : ∀ i, IsFppfTorsor 𝒞 S hS (Bᵢ i) (hBᵢ i)
      ((Over.pullback (f i)).obj G) ((Over.pullback (f i)).obj X)
      (isAlgebraicSpace_pullback 𝒞 S hS G.hom (f i) hG (hBᵢ i) hB)
      (isAlgebraicSpace_pullback 𝒞 S hS X.hom (f i) hX (hBᵢ i) hB)) :
    IsFppfTorsor 𝒞 S hS B hB G X hG hX := by
  classical
  choose J Bᵢⱼ g hBᵢⱼ hcovᵢ hsec using fun i => (htriv i).2
  refine ⟨hp, Σ i, J i, fun p => Bᵢⱼ p.1 p.2, fun p => g p.1 p.2 ≫ f p.1,
    fun p => hBᵢⱼ p.1 p.2,
    isFppfCovering_comp 𝒞 S hS I J Bᵢ Bᵢⱼ f g hcov hcovᵢ, fun p => ?_⟩
  obtain ⟨t, ht⟩ := (nonempty_unitHom_pullback_iff (g p.1 p.2)
    ((Over.pullback (f p.1)).obj X)).1 (hsec p.1 p.2)
  refine (nonempty_unitHom_pullback_iff (g p.1 p.2 ≫ f p.1) X).2
    ⟨t ≫ pullback.fst X.hom (f p.1), ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ f p.1) ht

/-! ### Locality of the pseudo-torsor condition -/

variable (𝒞 S hS) in
/-- If every section of the base over a test object of the big fppf site lifts to a member of a
family of morphisms to the base, and the restriction of the action to every member is a
pseudo-torsor, then the action is a pseudo-torsor. -/
theorem isPseudoTorsor_of_forall_exists_lift (G X : Over B) [GrpObj G] [ModObj G X]
    {I : Type v} (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, Bᵢ i ⟶ B)
    (hlift : ∀ (T : BigFppfOver 𝒞 S hS) (c : yoneda.obj T ⟶ B),
      ∃ (i : I) (c' : yoneda.obj T ⟶ Bᵢ i), c' ≫ f i = c)
    (h : ∀ i, IsPseudoTorsor ((Over.pullback (f i)).obj G) ((Over.pullback (f i)).obj X)) :
    IsPseudoTorsor G X := by
  refine (isPseudoTorsor_iff_points 𝒞 S hS B G X).2 fun T c x y => ?_
  obtain ⟨i, c', hc⟩ := hlift T c
  subst hc
  obtain ⟨g, hg, huniq⟩ := (isPseudoTorsor_iff_points 𝒞 S hS (Bᵢ i)
    ((Over.pullback (f i)).obj G) ((Over.pullback (f i)).obj X)).1 (h i) T c'
    ((pullbackHomEquiv (f i) X c').symm x)
    ((pullbackHomEquiv (f i) X c').symm y)
  refine ⟨pullbackHomEquiv (f i) G c' g, ?_, ?_⟩
  · calc
      pullbackHomEquiv (f i) G c' g • x
          = pullbackHomEquiv (f i) X c'
            (g • (pullbackHomEquiv (f i) X c').symm x) := by
        rw [pullbackHomEquiv_smul, Equiv.apply_symm_apply]
      _ = y := by rw [hg, Equiv.apply_symm_apply]
  · intro g' hg'
    have h1 : (pullbackHomEquiv (f i) G c').symm g' •
        (pullbackHomEquiv (f i) X c').symm x =
        (pullbackHomEquiv (f i) X c').symm y := by
      apply (pullbackHomEquiv (f i) X c').injective
      rw [pullbackHomEquiv_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
      exact hg'
    rw [← huniq _ h1, Equiv.apply_symm_apply]

variable (𝒞 S hS) in
/-- An action whose restriction to every member of an fppf covering of the base is an fppf
torsor, and such that every section of the base lifts to a member, is an fppf torsor. -/
theorem isFppfTorsor_of_forall_exists_lift (hB : IsAlgebraicSpace 𝒞 S hS B) (G X : Over B)
    [GrpObj G] [ModObj G X] (hG : IsAlgebraicSpace 𝒞 S hS G.left)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left)
    {I : Type (u + 1)} (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, Bᵢ i ⟶ B)
    (hBᵢ : ∀ i, IsAlgebraicSpace 𝒞 S hS (Bᵢ i)) (hcov : IsFppfCovering 𝒞 S hS Bᵢ f)
    (hlift : ∀ (T : BigFppfOver 𝒞 S hS) (c : yoneda.obj T ⟶ B),
      ∃ (i : I) (c' : yoneda.obj T ⟶ Bᵢ i), c' ≫ f i = c)
    (htriv : ∀ i, IsFppfTorsor 𝒞 S hS (Bᵢ i) (hBᵢ i)
      ((Over.pullback (f i)).obj G) ((Over.pullback (f i)).obj X)
      (isAlgebraicSpace_pullback 𝒞 S hS G.hom (f i) hG (hBᵢ i) hB)
      (isAlgebraicSpace_pullback 𝒞 S hS X.hom (f i) hX (hBᵢ i) hB)) :
    IsFppfTorsor 𝒞 S hS B hB G X hG hX :=
  isFppfTorsor_of_restrict 𝒞 S hS hB G X hG hX
    (isPseudoTorsor_of_forall_exists_lift 𝒞 S hS G X Bᵢ f hlift fun i => (htriv i).1)
    Bᵢ f hBᵢ hcov htriv

/-! ### Local liftability of a section of the base along an fppf covering -/

variable (𝒞 S hS) in
/-- A section of the base over a test object of the big fppf site factors through a member of
an fppf covering family of the base after passing to a covering sieve of the test object. -/
theorem exists_sieve_lift_of_isFppfCovering {I : Type (u + 1)}
    (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, Bᵢ i ⟶ B)
    (hcov : IsFppfCovering 𝒞 S hS Bᵢ f) (T : BigFppfOver 𝒞 S hS) (c : yoneda.obj T ⟶ B) :
    ∃ R ∈ BigFppfOver.topology 𝒞 S hS T,
      ∀ ⦃W : BigFppfOver 𝒞 S hS⦄ (k : W ⟶ T), R k →
        ∃ (i : I) (c' : yoneda.obj W ⟶ Bᵢ i), c' ≫ f i = yoneda.map k ≫ c := by
  classical
  have hP : IsFppfCovering 𝒞 S hS (fun i => pullback c (f i))
      (fun i => pullback.fst c (f i)) :=
    isFppfCovering_fibreProduct 𝒞 S hS
      (X := (⟨B, hcov.target_isAlgebraicSpace⟩ : AlgebraicSpaces 𝒞 S hS))
      (X' := (⟨yoneda.obj T, isAlgebraicSpace_yoneda 𝒞 S hS T⟩ : AlgebraicSpaces 𝒞 S hS))
      (fun i => (⟨Bᵢ i, hcov.source_isAlgebraicSpace i⟩ : AlgebraicSpaces 𝒞 S hS))
      (fun i => ObjectProperty.homMk (f i)) (ObjectProperty.homMk c) hcov
  obtain ⟨V, a, hV⟩ := exists_fppfCovering_scheme_refinement 𝒞 S hS _ _ hP
  let q (i : I) : V i ⟶ T := yoneda.preimage (a i ≫ pullback.fst c (f i))
  have hq (i : I) : yoneda.map (q i) = a i ≫ pullback.fst c (f i) := by simp [q]
  have hVq : IsFppfCovering 𝒞 S hS (fun i => yoneda.obj (V i))
      (fun i => yoneda.map (q i)) := by
    simpa only [hq] using hV
  let E : PreZeroHypercover.{u + 1} T.left :=
    ⟨I, fun i => (V i).left, fun i => (q i).left⟩
  have hE : AlgebraicGeometry.IsFppfCovering (⟨T.left, E⟩ : Covering 𝒞.Schemes) := by
    rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
      ← PreZeroHypercover.presieve₀_map]
    exact yoneda_fppfCovering_mem_fppfPrecoverage 𝒞 S hS V T q hVq
  refine ⟨Sieve.ofArrows V q, ?_, ?_⟩
  · rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    simpa [E, PreZeroHypercover.presieve₀] using
      𝒞.generate_mem_topology_of_isFppfCovering E hE
  · intro W k hk
    obtain ⟨i, e, he⟩ := Sieve.ofArrows.exists hk
    refine ⟨i, yoneda.map e ≫ a i ≫ pullback.snd c (f i), ?_⟩
    subst he
    rw [Functor.map_comp, hq i]
    simp [pullback.condition]

/-! ### Gluing the local group elements -/

/-- The morphism of the slice over `B` from the test object presented by a section of the base
restricted along a morphism `k` of the site to the test object presented by that section. -/
private def yonedaOverRestrict {T W : BigFppfOver 𝒞 S hS} (c : yoneda.obj T ⟶ B)
    (k : W ⟶ T) : (Over.mk (yoneda.map k ≫ c) : Over B) ⟶ Over.mk c :=
  Over.homMk (yoneda.map k) rfl

@[simp]
private theorem yonedaOverRestrict_left {T W : BigFppfOver 𝒞 S hS} (c : yoneda.obj T ⟶ B)
    (k : W ⟶ T) : (yonedaOverRestrict c k).left = yoneda.map k :=
  rfl

/-- The morphism of the slice over `B` relating two restrictions of a section of the base
along a factorization `l ≫ k = m` of morphisms of the site. -/
private def yonedaOverRestrictFactor {T W Z : BigFppfOver 𝒞 S hS} (c : yoneda.obj T ⟶ B)
    {k : W ⟶ T} {m : Z ⟶ T} (l : Z ⟶ W) (hm : l ≫ k = m) :
    (Over.mk (yoneda.map m ≫ c) : Over B) ⟶ Over.mk (yoneda.map k ≫ c) :=
  Over.homMk (yoneda.map l) (by subst hm; simp)

@[simp]
private theorem yonedaOverRestrictFactor_left {T W Z : BigFppfOver 𝒞 S hS}
    (c : yoneda.obj T ⟶ B) {k : W ⟶ T} {m : Z ⟶ T} (l : Z ⟶ W) (hm : l ≫ k = m) :
    (yonedaOverRestrictFactor c l hm).left = yoneda.map l :=
  rfl

private theorem yonedaOverRestrictFactor_comp {T W Z : BigFppfOver 𝒞 S hS}
    (c : yoneda.obj T ⟶ B) {k : W ⟶ T} {m : Z ⟶ T} (l : Z ⟶ W) (hm : l ≫ k = m) :
    yonedaOverRestrictFactor c l hm ≫ yonedaOverRestrict c k = yonedaOverRestrict c m := by
  subst hm
  apply Over.OverMorphism.ext
  simp

/-- Two sections of a sheaf on the big fppf site over `S` that agree after restriction along
every morphism of a covering sieve are equal. -/
private theorem eq_of_restriction_eq_on_sieve {P : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    (hP : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) P) {T : BigFppfOver 𝒞 S hS}
    {R : Sieve T} (hR : R ∈ BigFppfOver.topology 𝒞 S hS T) {s t : P.obj (op T)}
    (hst : ∀ ⦃W : BigFppfOver 𝒞 S hS⦄ (k : W ⟶ T), R k → P.map k.op s = P.map k.op t) :
    s = t :=
  (((isSheaf_iff_isSheaf_of_type _ _).1 hP) R hR).isSeparatedFor
    (fun _ k _ => P.map k.op s) s t (fun _ _ _ => rfl) (fun _ k hk => (hst k hk).symm)

variable (𝒞 S hS) in
/-- The unique group element carrying one point of `X` to another over a section of the base
which factors through a morphism `f₀` along which the action restricts to a pseudo-torsor. -/
private theorem existsUnique_smul_of_lift (G X : Over B) [GrpObj G] [ModObj G X]
    {B₀ : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (f₀ : B₀ ⟶ B)
    (hp : IsPseudoTorsor ((Over.pullback f₀).obj G) ((Over.pullback f₀).obj X))
    (T : BigFppfOver 𝒞 S hS) {c : yoneda.obj T ⟶ B} (c' : yoneda.obj T ⟶ B₀)
    (hc : c' ≫ f₀ = c) (x y : (Over.mk c : Over B) ⟶ X) :
    ∃! g : (Over.mk c : Over B) ⟶ G, g • x = y := by
  subst hc
  obtain ⟨g, hg, huniq⟩ := (isPseudoTorsor_iff_points 𝒞 S hS B₀
    ((Over.pullback f₀).obj G) ((Over.pullback f₀).obj X)).1 hp T c'
    ((pullbackHomEquiv f₀ X c').symm x) ((pullbackHomEquiv f₀ X c').symm y)
  refine ⟨pullbackHomEquiv f₀ G c' g, ?_, ?_⟩
  · calc
      pullbackHomEquiv f₀ G c' g • x
          = pullbackHomEquiv f₀ X c' (g • (pullbackHomEquiv f₀ X c').symm x) := by
        rw [pullbackHomEquiv_smul, Equiv.apply_symm_apply]
      _ = y := by rw [hg, Equiv.apply_symm_apply]
  · intro g' hg'
    have h1 : (pullbackHomEquiv f₀ G c').symm g' • (pullbackHomEquiv f₀ X c').symm x =
        (pullbackHomEquiv f₀ X c').symm y := by
      apply (pullbackHomEquiv f₀ X c').injective
      rw [pullbackHomEquiv_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
      exact hg'
    rw [← huniq _ h1, Equiv.apply_symm_apply]

variable (𝒞 S hS) in
/-- An action whose restriction to every member of an fppf covering of the base is a
pseudo-torsor is a pseudo-torsor. -/
theorem isPseudoTorsor_of_isFppfCovering (G X : Over B) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace 𝒞 S hS G.left) (hX : IsAlgebraicSpace 𝒞 S hS X.left)
    {I : Type (u + 1)} (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, Bᵢ i ⟶ B)
    (hcov : IsFppfCovering 𝒞 S hS Bᵢ f)
    (h : ∀ i, IsPseudoTorsor ((Over.pullback (f i)).obj G) ((Over.pullback (f i)).obj X)) :
    IsPseudoTorsor G X := by
  classical
  refine (isPseudoTorsor_iff_points 𝒞 S hS B G X).2 fun T c x y => ?_
  obtain ⟨R, hR, hlift⟩ := exists_sieve_lift_of_isFppfCovering 𝒞 S hS Bᵢ f hcov T c
  have key : ∀ (W : BigFppfOver 𝒞 S hS) (k : W ⟶ T), R k →
      ∃! g : (Over.mk (yoneda.map k ≫ c) : Over B) ⟶ G,
        g • (yonedaOverRestrict c k ≫ x) = yonedaOverRestrict c k ≫ y := by
    intro W k hk
    obtain ⟨i, c', hc'⟩ := hlift k hk
    exact existsUnique_smul_of_lift 𝒞 S hS G X (f i) (h i) W c' hc' _ _
  choose gl hgl₀ hglu₀ using key
  have hgl : ∀ (W : BigFppfOver 𝒞 S hS) (k : W ⟶ T) (hk : R k),
      gl W k hk • (yonedaOverRestrict c k ≫ x) = yonedaOverRestrict c k ≫ y :=
    fun W k hk => hgl₀ W k hk
  have hglu : ∀ (W : BigFppfOver 𝒞 S hS) (k : W ⟶ T) (hk : R k)
      (g : (Over.mk (yoneda.map k ≫ c) : Over B) ⟶ G),
      g • (yonedaOverRestrict c k ≫ x) = yonedaOverRestrict c k ≫ y → g = gl W k hk :=
    fun W k hk g hg => hglu₀ W k hk g hg
  have hres : ∀ (W Z : BigFppfOver 𝒞 S hS) (k : W ⟶ T) (hk : R k) (l : Z ⟶ W)
      (m : Z ⟶ T) (hm : l ≫ k = m) (hmR : R m),
      yoneda.map l ≫ (gl W k hk).left = (gl Z m hmR).left := by
    intro W Z k hk l m hm hmR
    have hfac : yonedaOverRestrictFactor c l hm ≫ gl W k hk = gl Z m hmR := by
      refine hglu Z m hmR _ ?_
      rw [← yonedaOverRestrictFactor_comp c l hm]
      simp only [Category.assoc]
      rw [← ModObj.comp_smul, hgl W k hk]
    simpa using congrArg Over.Hom.left hfac
  have hfam : Presieve.FamilyOfElements.Compatible
      (P := G.left) (X := T) (R := R.arrows)
      (fun W k hk => yonedaEquiv (gl W k hk).left) := by
    intro W₁ W₂ Z l₁ l₂ k₁ k₂ h₁ h₂ hcomm
    have hmR : R (l₁ ≫ k₁) := R.downward_closed h₁ l₁
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    exact congrArg yonedaEquiv
      ((hres W₁ Z k₁ h₁ l₁ _ rfl hmR).trans (hres W₂ Z k₂ h₂ l₂ _ hcomm.symm hmR).symm)
  obtain ⟨sG, hsG₀, -⟩ := ((isSheaf_iff_isSheaf_of_type _ _).1 hG.isSheaf) R hR _ hfam
  have hsG : ∀ (W : BigFppfOver 𝒞 S hS) (k : W ⟶ T) (hk : R k),
      G.left.map k.op sG = yonedaEquiv (gl W k hk).left := fun W k hk => hsG₀ k hk
  have hgsec : ∀ (W : BigFppfOver 𝒞 S hS) (k : W ⟶ T) (hk : R k),
      yoneda.map k ≫ yonedaEquiv.symm sG = (gl W k hk).left := by
    intro W k hk
    rw [yonedaEquiv_symm_naturality_left, hsG W k hk, Equiv.symm_apply_apply]
  have hgstruct : yonedaEquiv.symm sG ≫ G.hom = c := by
    apply yonedaEquiv.injective
    refine eq_of_restriction_eq_on_sieve hcov.target_isAlgebraicSpace.isSheaf hR
      fun W k hk => ?_
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality, ← Category.assoc, hgsec W k hk]
    exact congrArg yonedaEquiv (Over.w (gl W k hk))
  refine ⟨Over.homMk (yonedaEquiv.symm sG) hgstruct, ?_, ?_⟩
  · have hgres : ∀ (W : BigFppfOver 𝒞 S hS) (k : W ⟶ T) (hk : R k),
        yonedaOverRestrict c k ≫
            (Over.homMk (yonedaEquiv.symm sG) hgstruct : (Over.mk c : Over B) ⟶ G) =
          gl W k hk := fun W k hk => Over.OverMorphism.ext (by simpa using hgsec W k hk)
    apply Over.OverMorphism.ext
    apply yonedaEquiv.injective
    refine eq_of_restriction_eq_on_sieve hX.isSheaf hR fun W k hk => ?_
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    refine congrArg yonedaEquiv ?_
    have hstep : yonedaOverRestrict c k ≫
        ((Over.homMk (yonedaEquiv.symm sG) hgstruct : (Over.mk c : Over B) ⟶ G) • x) =
        yonedaOverRestrict c k ≫ y := by
      rw [ModObj.comp_smul, hgres W k hk, hgl W k hk]
    simpa using congrArg Over.Hom.left hstep
  · intro g' hg'
    apply Over.OverMorphism.ext
    apply yonedaEquiv.injective
    refine eq_of_restriction_eq_on_sieve hG.isSheaf hR fun W k hk => ?_
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    refine congrArg yonedaEquiv ?_
    have h1 : yonedaOverRestrict c k ≫ g' = gl W k hk := by
      refine hglu W k hk _ ?_
      rw [← ModObj.comp_smul, hg']
    have h2 := congrArg Over.Hom.left h1
    simp only [Over.comp_left, yonedaOverRestrict_left] at h2
    simpa [h2] using (hgsec W k hk).symm

variable (𝒞 S hS) in
/-- An action whose restriction to every member of an fppf covering of the base is an fppf
torsor is an fppf torsor. -/
theorem isFppfTorsor_of_isFppfCovering (hB : IsAlgebraicSpace 𝒞 S hS B) (G X : Over B)
    [GrpObj G] [ModObj G X] (hG : IsAlgebraicSpace 𝒞 S hS G.left)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left)
    {I : Type (u + 1)} (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, Bᵢ i ⟶ B)
    (hBᵢ : ∀ i, IsAlgebraicSpace 𝒞 S hS (Bᵢ i)) (hcov : IsFppfCovering 𝒞 S hS Bᵢ f)
    (htriv : ∀ i, IsFppfTorsor 𝒞 S hS (Bᵢ i) (hBᵢ i)
      ((Over.pullback (f i)).obj G) ((Over.pullback (f i)).obj X)
      (isAlgebraicSpace_pullback 𝒞 S hS G.hom (f i) hG (hBᵢ i) hB)
      (isAlgebraicSpace_pullback 𝒞 S hS X.hom (f i) hX (hBᵢ i) hB)) :
    IsFppfTorsor 𝒞 S hS B hB G X hG hX :=
  isFppfTorsor_of_restrict 𝒞 S hS hB G X hG hX
    (isPseudoTorsor_of_isFppfCovering 𝒞 S hS G X hG hX Bᵢ f hcov fun i => (htriv i).1)
    Bᵢ f hBᵢ hcov htriv

end AlgebraicGeometry.Space

end

