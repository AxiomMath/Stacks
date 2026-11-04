module

public import StacksFrontier.AlgebraicGeometry.Etale.SmoothCoverClosedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningExtensionSmooth
public import StacksFrontier.Deformation.Artin.RimSchlessinger.CoconeUniqueFlat
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FromThickeningPushouts
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Slice

/-!
# Algebraic stacks satisfy (RS) at squares inducing isomorphisms on residue fields

Let `𝒳` be an algebraic stack over `S` and consider a square of condition (RS) of Tag 07WP: a
pushout `Y' = Y ⨿_X X'` of spectra of Artinian local rings of finite type over `S` along a closed
immersion `X ⟶ X'`. Suppose moreover that `X ⟶ Y` induces an isomorphism of residue fields.
Then the comparison functor `𝒳_{Y'} ⟶ 𝒳_Y ×_{𝒳_X} 𝒳_{X'}` is an equivalence.

Full faithfulness holds for every category fibred in groupoids with representable diagonal
(`Deformation.Artin.fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal`). For
essential surjectivity let `(y, x', φ)` be an object of the two-fibre product, and choose a smooth
surjective presentation `f : (Sch/U) ⟶ 𝒳`. All four corners have one closed point, with the same
residue field `κ`. The proof follows the source (Tag 07WN) with the pushout of algebraic spaces
replaced by two étale neighbourhoods of the closed point of `Y'`:

1. `y` lifts to `U` after a smooth surjective base change of `Y`, and after an étale base change
   `Z₁ ⟶ Y'` whose fibre over the closed point is the spectrum of a finite separable extension
   `κ₁` of `κ`, the smooth base change has a section over `Y ×_{Y'} Z₁`
   (`AlgebraicGeometry.exists_etale_section_of_smooth_of_closedPoint`);
2. the restriction of that lift to `X ×_{Y'} Z₁` extends across the thickening into `X'` after a
   smooth surjective base change
   (`AlgebraicGeometry.Stack.exists_smooth_extension_of_isFiniteOrderThickening`), and a second
   étale neighbourhood `Z₂ ⟶ Z₁` of the closed point provides the section of that base change over
   `X ×_{Y'} Z₂`;
3. over `Z₂` the two lifts to `U` glue along the pushout of schemes, giving an object of `𝒳`
   over `Z₂` with the required restrictions, i.e. a cocone over the restricted span;
4. cocones descend along the étale covering `Z₂ ⟶ Y'`, being unique on its overlaps by full
   faithfulness at flat base changes
   (`CategoryTheory.Functor.IsStackInGroupoids.nonempty_cocone_of_baseChange`).

The hypothesis on residue fields is what makes the closed point of every corner the closed point
of `Y'`, so that the étale neighbourhoods produced on `Y` and on `X ×_{Y'} Z₁` come from étale
neighbourhoods of `Y'` and of `Z₁`.

## Main results

* `Deformation.Artin.essSurj_fiberSquareComparison_of_residueField`: the essential surjectivity.
* `Deformation.Artin.satisfiesRSOfResidue_of_isAlgebraicStack`: an algebraic stack satisfies
  condition (RS) at the squares inducing surjections of residue fields.
* `Deformation.Artin.isDeformationCategory_predeformationCategory_of_isAlgebraicStack`: the
  predeformation category of a finite-type field-valued point of an algebraic stack is a
  deformation category.

## References

* [Stacks Project, Tag 07WN](https://stacks.math.columbia.edu/tag/07WN)
* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u w

namespace Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Pushouts of the site detected on schemes -/

/-- **A square of the big fppf site whose square of schemes is a pushout is a pushout.** -/
theorem isPushout_of_isPushout_toScheme {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X')
    (j : X ⟶ Y) (i' : X' ⟶ Y') (j' : Y ⟶ Y') (w : i ≫ i' = j ≫ j')
    (hpo : IsPushout ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map j)
      ((BigFppfOver.toScheme B S hS).map i') ((BigFppfOver.toScheme B S hS).map j')) :
    IsPushout i j i' j' := by
  have key := fun s : PushoutCocone i j =>
    (pushout_test_over B.inclusion i j i' j' hpo s.pt).2 s.inr s.inl s.condition.symm
  choose g hg using key
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk _ g (fun s => (hg s).2)
    (fun s => (hg s).1) fun s m h₁ h₂ => ?_)
  refine (pushout_test_over B.inclusion i j i' j' hpo s.pt).1 _ _ ?_ ?_
  · rw [h₂]
    exact (hg s).1.symm
  · rw [h₁]
    exact (hg s).2.symm

/-! ### Étale neighbourhoods of a closed point inside the site -/

/-- A quasi-compact scheme with a morphism locally of finite type to an object of the site is
itself an object of the site. -/
alias contains_of_locallyOfFiniteType := AlgebraicGeometry.contains_of_locallyOfFiniteType

/-- **A smooth surjective morphism of the site has a section after an étale base change
through a closed point.** The site form of
`AlgebraicGeometry.exists_etale_section_of_smooth_of_closedPoint`. -/
theorem exists_etale_section_of_smooth_of_closedPoint_site {Z T T₀ : BigFppfOver B S hS}
    (t : T ⟶ Z) (m : T₀ ⟶ T) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    (hm : Smooth ((BigFppfOver.toScheme B S hS).map m))
    (hms : Surjective ((BigFppfOver.toScheme B S hS).map m))
    {K : Type u} [Field K] (c : Spec (.of K) ⟶ (BigFppfOver.toScheme B S hS).obj Z)
    [IsClosedImmersion c] (p : Spec (.of K) ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hp : Stacks.Thickenings.IsFiniteOrderThickening p)
    (hpt : p ≫ (BigFppfOver.toScheme B S hS).map t = c) :
    ∃ (K₁ : Type u) (_ : Field K₁) (Z₁ : BigFppfOver B S hS) (τ : Z₁ ⟶ Z)
      (c₁ : Spec (.of K₁) ⟶ (BigFppfOver.toScheme B S hS).obj Z₁)
      (e₁ : Spec (.of K₁) ⟶ Spec (.of K)),
      (∃ _ : Algebra K K₁, Module.Finite K K₁ ∧ Algebra.IsSeparable K K₁ ∧
        e₁ = Spec.map (CommRingCat.ofHom (algebraMap K K₁))) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z₁) ∧
      Etale ((BigFppfOver.toScheme B S hS).map τ) ∧
      IsPullback e₁ c₁ c ((BigFppfOver.toScheme B S hS).map τ) ∧
      ∃ r : pullback t τ ⟶ T₀, r ≫ m = pullback.fst t τ := by
  let toS := BigFppfOver.toScheme B S hS
  have := hm
  have := hms
  obtain ⟨K₁, _, Z₁s, τs, c₁, e₁, hsep, hZ₁, hτ, hpb, r, hr⟩ :=
    exists_etale_section_of_smooth_of_closedPoint (toS.map t) (toS.map m) c p hp hpt
  have := hZ₁
  have := hτ
  have hcont : B.Contains Z₁s := contains_of_locallyOfFiniteType B (U := Z.left) τs
  let Z₁ : BigFppfOver B S hS := Over.mk (ObjectProperty.homMk (P := B.Contains)
    (X := B.obj hcont) τs ≫ Z.hom)
  let τ : Z₁ ⟶ Z := Over.homMk (ObjectProperty.homMk τs) rfl
  have hτS : toS.map τ = τs := rfl
  refine ⟨K₁, inferInstance, Z₁, τ, c₁, e₁, hsep, hZ₁, hτ, hpb, ?_⟩
  have : PreservesLimitsOfShape WalkingCospan toS :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  let e := PreservesPullback.iso toS t τ
  let r' : pullback (toS.map t) (toS.map τ) ⟶ toS.obj T₀ := r
  have hr' : r' ≫ toS.map m = pullback.fst (toS.map t) (toS.map τ) := hr
  let rs : toS.obj (pullback t τ) ⟶ toS.obj T₀ := e.hom ≫ r'
  have hrs : rs ≫ toS.map m = toS.map (pullback.fst t τ) := by
    show e.hom ≫ r' ≫ toS.map m = _
    rw [hr']
    exact PreservesPullback.iso_hom_fst toS t τ
  let rl : (pullback t τ).left ⟶ T₀.left := ObjectProperty.homMk rs
  have hrl : rl ≫ T₀.hom = (pullback t τ).hom := by
    rw [← Over.w m, ← Over.w (pullback.fst t τ), ← Category.assoc]
    congr 1
    exact B.inclusion.map_injective hrs
  exact ⟨Over.homMk rl hrl, Over.OverMorphism.ext (B.inclusion.map_injective hrs)⟩

/-- **The closed point of a base change.** If `c : Spec K ⟶ Z` factors through `T` by a
finite-order thickening `p`, and `c₁ : Spec K₁ ⟶ Z₁` is the base change of `c` along `τ`, then
`c₁` factors through `T ×_Z Z₁` by a finite-order thickening. -/
theorem exists_closedPoint_pullback {Z Z₁ T : BigFppfOver B S hS} (t : T ⟶ Z) (τ : Z₁ ⟶ Z)
    {K K₁ : Type u} [Field K] [Field K₁] (c : Spec (.of K) ⟶ (BigFppfOver.toScheme B S hS).obj Z)
    (c₁ : Spec (.of K₁) ⟶ (BigFppfOver.toScheme B S hS).obj Z₁) (e₁ : Spec (.of K₁) ⟶ Spec (.of K))
    (hpb : IsPullback e₁ c₁ c ((BigFppfOver.toScheme B S hS).map τ))
    (p : Spec (.of K) ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hp : Stacks.Thickenings.IsFiniteOrderThickening p)
    (hpt : p ≫ (BigFppfOver.toScheme B S hS).map t = c) :
    ∃ p₁ : Spec (.of K₁) ⟶ (BigFppfOver.toScheme B S hS).obj (pullback t τ),
      Stacks.Thickenings.IsFiniteOrderThickening p₁ ∧
      p₁ ≫ (BigFppfOver.toScheme B S hS).map (pullback.snd t τ) = c₁ ∧
      p₁ ≫ (BigFppfOver.toScheme B S hS).map (pullback.fst t τ) = e₁ ≫ p := by
  let toS := BigFppfOver.toScheme B S hS
  have : PreservesLimitsOfShape WalkingCospan toS :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  let e := PreservesPullback.iso toS t τ
  let q : Spec (.of K₁) ⟶ pullback (toS.map t) (toS.map τ) :=
    pullback.lift (e₁ ≫ p) c₁ (by rw [Category.assoc, hpt, hpb.w])
  have hq : IsPullback q e₁ (pullback.fst (toS.map t) (toS.map τ)) p := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback _ _).flip
    rw [pullback.lift_snd, hpt]
    exact hpb.flip
  have hfst : e.inv ≫ toS.map (pullback.fst t τ) = pullback.fst (toS.map t) (toS.map τ) :=
    (Iso.inv_comp_eq _).2 (PreservesPullback.iso_hom_fst toS t τ).symm
  have hsnd : e.inv ≫ toS.map (pullback.snd t τ) = pullback.snd (toS.map t) (toS.map τ) :=
    (Iso.inv_comp_eq _).2 (PreservesPullback.iso_hom_snd toS t τ).symm
  have hq' : IsPullback (q ≫ e.inv) e₁ (toS.map (pullback.fst t τ)) p :=
    IsPullback.of_iso hq (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [← hfst]) (by simp)
  refine ⟨q ≫ e.inv, Stacks.Thickenings.isFiniteOrderThickening_of_isPullback hq' hp, ?_, ?_⟩
  · rw [Category.assoc, hsnd, pullback.lift_snd]
  · rw [Category.assoc, hfst, pullback.lift_fst]

/-! ### Facts about squares of Artinian local schemes -/

section Facts

/-- **Global sections take pushouts of schemes to pullbacks of rings**, the functor of global
sections being a left adjoint `Schemeᵒᵖ`-valued functor. -/
theorem isPullback_appTop_of_isPushout {X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : X ⟶ Y}
    {i' : X' ⟶ Y'} {j' : Y ⟶ Y'} (h : IsPushout i j i' j') :
    IsPullback j'.appTop i'.appTop j.appTop i.appTop := by
  have : PreservesColimitsOfSize.{0, 0} Scheme.Γ.{u}.rightOp :=
    ΓSpec.adjunction.leftAdjoint_preservesColimits
  exact (h.map Scheme.Γ.rightOp).unop

/-- **A closed immersion from a nonempty scheme into the spectrum of an Artinian local ring is a
finite-order thickening**: its kernel is a proper ideal, hence contained in the nilpotent
maximal ideal. -/
theorem isFiniteOrderThickening_of_isClosedImmersion {T T' : Scheme.{u}} [IsAffine T']
    (p : T ⟶ T') [IsClosedImmersion p] [Nonempty T] [IsLocalRing Γ(T', ⊤)]
    [IsArtinianRing Γ(T', ⊤)] : Stacks.Thickenings.IsFiniteOrderThickening p := by
  have hT : IsAffine T := (IsClosedImmersion.isAffine_surjective_of_isAffine p).1
  have : Nontrivial Γ(T, ⊤) := by
    obtain ⟨t⟩ := ‹Nonempty T›
    let P := IsAffineOpen.primeIdealOf (U := ⊤) (isAffineOpen_top T) ⟨t, trivial⟩
    refine ⟨⟨0, 1, fun h => P.isPrime.ne_top ?_⟩⟩
    rw [Ideal.eq_top_iff_one, ← h]
    exact P.asIdeal.zero_mem
  have hne : RingHom.ker p.appTop.hom ≠ ⊤ := by
    intro htop
    have : (1 : Γ(T', ⊤)) ∈ RingHom.ker p.appTop.hom := htop ▸ Submodule.mem_top
    exact one_ne_zero ((RingHom.mem_ker).1 this |>.symm ▸ (map_one p.appTop.hom).symm)
  have hle : RingHom.ker p.appTop.hom ≤ (⊥ : Ideal Γ(T', ⊤)).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hne
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := Γ(T', ⊤))
  refine ⟨inferInstance, n, ?_⟩
  rw [Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine]
  refine le_bot_iff.mp ?_
  calc RingHom.ker p.appTop.hom ^ (n + 1) ≤ RingHom.ker p.appTop.hom ^ n :=
        Ideal.pow_le_pow_right (Nat.le_succ n)
    _ ≤ (⊥ : Ideal Γ(T', ⊤)).jacobson ^ n := Ideal.pow_right_mono hle n
    _ = ⊥ := by rw [hn, Ideal.zero_eq_bot]

/-- Global sections of `Spec φ` followed by the inverse of the canonical isomorphism of an
affine scheme with the spectrum of its global sections. -/
theorem appTop_specMap_comp_isoSpec_inv {X : Scheme.{u}} [IsAffine X] {R : CommRingCat.{u}}
    (φ : Γ(X, ⊤) ⟶ R) :
    (Spec.map φ ≫ X.isoSpec.inv).appTop = φ ≫ (Scheme.ΓSpecIso R).inv := by
  have h₁ : X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
    rw [← cancel_mono (Scheme.ΓSpecIso Γ(X, ⊤)).hom, Iso.inv_hom_id]
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
    show (X.isoSpec.hom ≫ X.isoSpec.inv).appTop = _
    simp
  rw [Scheme.Hom.comp_appTop, h₁, ← cancel_mono (Scheme.ΓSpecIso R).hom, Category.assoc,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

end Facts

/-! ### Flat base change of a square and singleton coverings -/

section BaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- **Flat base change of a thickening square.** Let `Q` be a square of the site with affine
corners, cartesian square of global sections and finite-order thickening `Q.g`. Its base change
along a flat morphism from an affine object has the same three properties and is a pushout of
the site. -/
theorem baseChange_facts (Q : BaseSquare (BigFppfOver B S hS))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.W)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.Z)]
    (hΓ : IsPullback ((BigFppfOver.toScheme B S hS).map Q.i).appTop
      ((BigFppfOver.toScheme B S hS).map Q.j).appTop
      ((BigFppfOver.toScheme B S hS).map Q.f).appTop
      ((BigFppfOver.toScheme B S hS).map Q.g).appTop)
    (hg : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map Q.g))
    {Z' : BigFppfOver B S hS} (h : Z' ⟶ Q.Z) [IsAffine ((BigFppfOver.toScheme B S hS).obj Z')]
    [Flat ((BigFppfOver.toScheme B S hS).map h)] :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (Q.baseChange h).U) ∧
    IsAffine ((BigFppfOver.toScheme B S hS).obj (Q.baseChange h).V) ∧
    IsAffine ((BigFppfOver.toScheme B S hS).obj (Q.baseChange h).W) ∧
    IsPullback ((BigFppfOver.toScheme B S hS).map (Q.baseChange h).i).appTop
      ((BigFppfOver.toScheme B S hS).map (Q.baseChange h).j).appTop
      ((BigFppfOver.toScheme B S hS).map (Q.baseChange h).f).appTop
      ((BigFppfOver.toScheme B S hS).map (Q.baseChange h).g).appTop ∧
    Stacks.Thickenings.IsFiniteOrderThickening
      ((BigFppfOver.toScheme B S hS).map (Q.baseChange h).g) ∧
    IsPushout (Q.baseChange h).f (Q.baseChange h).g (Q.baseChange h).i (Q.baseChange h).j := by
  let T := BigFppfOver.toScheme B S hS
  let QB := Q.baseChange h
  let a := Q.baseChangeHom h
  have sY : IsPullback (T.map QB.i) (T.map a.aV) (T.map h) (T.map Q.i) :=
    (Q.isPullback_baseChange_i h).map T
  have sX' : IsPullback (T.map QB.j) (T.map a.aW) (T.map h) (T.map Q.j) :=
    (Q.isPullback_baseChange_j h).map T
  have sX : IsPullback (T.map QB.f) (T.map a.aU) (T.map a.aV) (T.map Q.f) :=
    (Q.isPullback_baseChange_f h).map T
  have sX'' : IsPullback (T.map QB.g) (T.map a.aU) (T.map a.aW) (T.map Q.g) :=
    (Q.isPullback_baseChange_g h).map T
  have hcomm : T.map QB.f ≫ T.map QB.i = T.map QB.g ≫ T.map QB.j := by
    rw [← T.map_comp, QB.w, T.map_comp]
  have : IsClosedImmersion (T.map Q.g) := hg.1
  have hV : IsAffine (T.obj QB.V) := IsAffine.of_isPullback sY
  have hW : IsAffine (T.obj QB.W) := IsAffine.of_isPullback sX'
  have hU : IsAffine (T.obj QB.U) := IsAffine.of_isPullback sX
  have hΓ' := isPullback_appTop_of_flat_baseChange (T.map Q.f) (T.map Q.g) (T.map Q.i)
    (T.map Q.j) (T.map h) (T.map QB.i) (T.map a.aV) (T.map QB.j) (T.map a.aW) (T.map QB.f)
    (T.map QB.g) (T.map a.aU) hΓ sY sX' sX sX'' hcomm
  have hpush := isPushout_of_flat_baseChange (T.map Q.f) (T.map Q.g) (T.map Q.i) (T.map Q.j)
    (T.map h) (T.map QB.i) (T.map a.aV) (T.map QB.j) (T.map a.aW) (T.map QB.f) (T.map QB.g)
    (T.map a.aU) hΓ sY sX' sX sX'' hcomm
  exact ⟨hU, hV, hW, hΓ', Stacks.Thickenings.isFiniteOrderThickening_of_isPullback sX'' hg,
    isPushout_of_isPushout_toScheme B S hS QB.f QB.g QB.i QB.j QB.w hpush⟩

/-- **A flat, locally finitely presented, surjective morphism is a covering on its own.** -/
theorem singleton_mem_topology {U V : BigFppfOver B S hS} (h : V ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B S hS).map h))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map h))
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map h)) {I : Type w} [Nonempty I] :
    Sieve.ofArrows (fun _ : I => V) (fun _ => h) ∈ BigFppfOver.topology B S hS U := by
  have hmem := mem_topology_of_family B S hS (I := PUnit.{u + 2}) (fun _ => V.left)
    (fun _ => h.left) (fun _ => hflat) (fun _ => hlfp)
    (fun x => ⟨PUnit.unit, hsurj.surj x⟩)
  refine GrothendieckTopology.superset_covering _ ?_ hmem
  rintro T g ⟨_, t, _, ⟨_⟩, rfl⟩
  obtain ⟨i⟩ := ‹Nonempty I›
  let e : (Over.mk (h.left ≫ U.hom) : BigFppfOver B S hS) ⟶ V :=
    Over.homMk (𝟙 _) (by simp [Over.w h])
  refine ⟨V, t ≫ e, h, ⟨i⟩, ?_⟩
  rw [Category.assoc]
  congr 1

end BaseChange

/-! ### Explicit forms of the lifting operations of a category fibred in groupoids -/

section Explicit

variable {𝒞 : Type*} [Category 𝒞] {𝒳 : Type*} [Category 𝒳] {p : 𝒳 ⥤ 𝒞}

/-- The fill-in of a category fibred in groupoids, with every lifting hypothesis explicit. -/
theorem exists_fill (hp : p.IsFiberedInGroupoids) {R R' S' : 𝒞} {f : R ⟶ S'} {g : R' ⟶ R}
    {f' : R' ⟶ S'} (hf' : f' = g ≫ f) {a a' b : 𝒳} (φ : a ⟶ b) (hφ : p.IsHomLift f φ)
    (φ' : a' ⟶ b) (hφ' : p.IsHomLift f' φ') :
    ∃ χ : a' ⟶ a, p.IsHomLift g χ ∧ χ ≫ φ = φ' :=
  ⟨@Functor.IsFiberedInGroupoids.fill _ _ _ _ _ hp _ _ _ _ _ _ hf' _ _ _ φ hφ φ' hφ',
    @Functor.IsFiberedInGroupoids.fill_isHomLift _ _ _ _ _ hp _ _ _ _ _ _ hf' _ _ _ φ hφ φ' hφ',
    @Functor.IsFiberedInGroupoids.fill_fac _ _ _ _ _ hp _ _ _ _ _ _ hf' _ _ _ φ hφ φ' hφ'⟩

/-- Uniqueness of fill-ins, with every lifting hypothesis explicit. -/
theorem hom_ext_explicit (hp : p.IsFiberedInGroupoids) {R R' S' : 𝒞} {f : R ⟶ S'}
    (g : R' ⟶ R) {a a' b : 𝒳} (φ : a ⟶ b) (hφ : p.IsHomLift f φ) {ψ ψ' : a' ⟶ a}
    (hψ : p.IsHomLift g ψ) (hψ' : p.IsHomLift g ψ') (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' :=
  @Functor.IsFiberedInGroupoids.hom_ext _ _ _ _ _ hp _ _ _ _ g _ _ _ φ hφ _ _ hψ hψ' h

/-- Composing with a lift of an identity on the right, with every hypothesis explicit. -/
theorem isHomLift_comp_id_right_explicit {R S' : 𝒞} {a b c : 𝒳} (f : R ⟶ S') (φ : a ⟶ b)
    (ψ : b ⟶ c) (hφ : p.IsHomLift f φ) (hψ : p.IsHomLift (𝟙 S') ψ) :
    p.IsHomLift f (φ ≫ ψ) := by
  simpa using @IsHomLift.comp _ _ _ _ _ _ _ _ _ _ _ f (𝟙 S') φ ψ hφ hψ

/-- Composing with a lift of an identity on the left, with every hypothesis explicit. -/
theorem isHomLift_comp_id_left_explicit {R S' : 𝒞} {a b c : 𝒳} (f : R ⟶ S') (φ : a ⟶ b)
    (ψ : b ⟶ c) (hφ : p.IsHomLift (𝟙 R) φ) (hψ : p.IsHomLift f ψ) :
    p.IsHomLift f (φ ≫ ψ) := by
  simpa using @IsHomLift.comp _ _ _ _ _ _ _ _ _ _ _ (𝟙 R) f φ ψ hφ hψ

/-- The image of a lift under a functor over the base, with every hypothesis explicit. -/
theorem isHomLift_map_explicit {𝒲 : Type*} [Category 𝒲] {q : 𝒲 ⥤ 𝒞} {F : 𝒲 ⥤ 𝒳}
    (hF : F ⋙ p = q) {R S' : 𝒞} {a b : 𝒲} (f : R ⟶ S') (φ : a ⟶ b) (hφ : q.IsHomLift f φ) :
    p.IsHomLift f (F.map φ) := by
  have := hφ
  exact isHomLift_map_of_comp_eq hF f φ

end Explicit

/-! ### Cocones from lifts to a presentation -/

section Cocone

open CategoryTheory.Functor

variable {𝒞 : Type*} [Category 𝒞] {𝒳 : Type*} [Category 𝒳] {p : 𝒳 ⥤ 𝒞}
  {Ucat : 𝒞} {F : Over Ucat ⥤ 𝒳} (hF : F ⋙ p = Over.forget Ucat)

include hF in
/-- **A span with a lift to a represented slice has a cocone at a pushout square.** If a span
`t` of a category fibred in groupoids over a pushout square receives, over the identity of the
square, a morphism from the image under `F` of a span of the slice over `Ucat`, then `t` has a
cocone: the span of the slice has one by the universal property of the pushout, and its image
pulls back along the morphism. -/
theorem nonempty_cocone_of_hom_map (hp : p.IsFiberedInGroupoids) (Q : BaseSquare 𝒞)
    (hpush : IsPushout Q.f Q.g Q.i Q.j) (t : SquareSpan p Q.f Q.g)
    (tU : SquareSpan (Over.forget Ucat) Q.f Q.g)
    (m : SquareSpan.Hom (BaseSquare.Hom.id Q) t (tU.map hF)) :
    Nonempty (t.Cocone Q.i Q.j) := by
  obtain ⟨cU⟩ := SquareSpan.nonempty_cocone_over_forget hpush tU
  obtain ⟨c', -, -⟩ := SquareSpan.exists_pull hp m (SquareSpan.Cocone.map hF cU)
  exact ⟨c'⟩

end Cocone


/-! ### The local cocone -/

section Local

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The local cocone.** Let `Q₁` be a square of the site with a span `s₁` over it, let `yv` be a
lift of `s₁.x` to a presentation `a` of `𝒳` through `ιY`, compatible with `s₁.u` through `θ`,
and suppose that the restriction of that lift along `Q₁.g` extends across thickenings after the
smooth base change `mX` (the extension property of
`AlgebraicGeometry.Stack.exists_smooth_extension_of_isFiniteOrderThickening`). If `mX` has a
section `rX` over the base change of `Q₁` to `τ₂`, and the base-changed square `Q₂` is a pushout
along a finite-order thickening of affine schemes, then every restriction of `s₁` to `Q₂` has a
cocone: the two lifts glue in the represented slice along the pushout. -/
theorem nonempty_cocone_of_extension (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    {Ub : BigFppfOver B S hS} (a : Stack.schemeStack.{u, w} B S hS Ub ⟶ 𝒳)
    (Q₁ : BaseSquare (BigFppfOver B S hS)) (s₁ : SquareSpan 𝒳.val.val.p Q₁.f Q₁.g)
    (yv : Q₁.V ⟶ Ub)
    (ιY : (CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk yv : Over Ub) ⟶ s₁.x)
    [hιY : 𝒳.val.val.p.IsHomLift (𝟙 Q₁.V) ιY]
    (θ : (CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (Q₁.f ≫ yv) : Over Ub) ⟶ s₁.u)
    [hθl : 𝒳.val.val.p.IsHomLift (𝟙 Q₁.U) θ]
    (hθ : θ ≫ s₁.α = (CatFiberedInGroupoids.homFunctor a.hom).map
      (Over.homMk Q₁.f rfl : (Over.mk (Q₁.f ≫ yv) : Over Ub) ⟶ Over.mk yv) ≫ ιY)
    {Tc : BigFppfOver B S hS} (mX : Tc ⟶ Q₁.U)
    (hext : ∀ {V V' : BigFppfOver B S hS} (j : V ⟶ V') (r : V ⟶ Tc) (r' : V' ⟶ Q₁.W),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V') →
      Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map j) →
      r ≫ mX ≫ Q₁.g = j ≫ r' →
      ∃ (z u' : (Stack.schemeStack.{u, w} B S hS Ub).val.val.obj) (μ : z ⟶ u')
        (ν : z ⟶ (Over.mk (Q₁.f ≫ yv) : Over Ub))
        (ψ : (CatFiberedInGroupoids.homFunctor a.hom).obj u' ⟶ s₁.y),
        (Stack.schemeStack.{u, w} B S hS Ub).val.val.p.IsHomLift j μ ∧
        (Stack.schemeStack.{u, w} B S hS Ub).val.val.p.IsHomLift (r ≫ mX) ν ∧
        𝒳.val.val.p.IsHomLift r' ψ ∧
        (CatFiberedInGroupoids.homFunctor a.hom).map μ ≫ ψ =
          (CatFiberedInGroupoids.homFunctor a.hom).map ν ≫ θ ≫ s₁.β)
    {Z₂ : BigFppfOver B S hS} (τ₂ : Z₂ ⟶ Q₁.Z) (rX : (Q₁.baseChange τ₂).U ⟶ Tc)
    (hrX : rX ≫ mX = (Q₁.baseChangeHom τ₂).aU)
    (hU₂ : IsAffine ((BigFppfOver.toScheme B S hS).obj (Q₁.baseChange τ₂).U))
    (hW₂ : IsAffine ((BigFppfOver.toScheme B S hS).obj (Q₁.baseChange τ₂).W))
    (hg₂ : Stacks.Thickenings.IsFiniteOrderThickening
      ((BigFppfOver.toScheme B S hS).map (Q₁.baseChange τ₂).g))
    (hpush₂ : IsPushout (Q₁.baseChange τ₂).f (Q₁.baseChange τ₂).g (Q₁.baseChange τ₂).i
      (Q₁.baseChange τ₂).j)
    (s₂ : SquareSpan 𝒳.val.val.p (Q₁.baseChange τ₂).f (Q₁.baseChange τ₂).g)
    (m₂ : SquareSpan.Hom (Q₁.baseChangeHom τ₂) s₂ s₁) :
    Nonempty (s₂.Cocone (Q₁.baseChange τ₂).i (Q₁.baseChange τ₂).j) := by
  let F := CatFiberedInGroupoids.homFunctor a.hom
  have hp := 𝒳.val.isFiberedInGroupoids
  let Q₂ := Q₁.baseChange τ₂
  let b := Q₁.baseChangeHom τ₂
  have hsq : rX ≫ mX ≫ Q₁.g = Q₂.g ≫ b.aW := by
    rw [← Category.assoc, hrX, b.wg]
  obtain ⟨z, u', μ, ν, ψ, hμ, hν, hψ, hcomp⟩ := hext Q₂.g rX b.aW hU₂ hW₂ hg₂ hsq
  have hO := Functor.IsFiberedInGroupoids.over_forget Ub
  have hF : F ⋙ 𝒳.val.val.p = Over.forget Ub := CatFiberedInGroupoids.homFunctor_comp_p a.hom
  rw [hrX] at hν
  have hμ' : (Over.forget Ub).IsHomLift Q₂.g μ := hμ
  have hν' : (Over.forget Ub).IsHomLift b.aU ν := hν
  -- the span of the slice over `Ub`
  let xU : Over Ub := Over.mk (b.aV ≫ yv)
  let cx : xU ⟶ Over.mk yv := Over.homMk b.aV rfl
  have hcx : (Over.forget Ub).IsHomLift b.aV cx := IsHomLift.of_fac' _ _ _ rfl rfl (by simp [cx])
  let fQ : (Over.mk (Q₁.f ≫ yv) : Over Ub) ⟶ Over.mk yv := Over.homMk Q₁.f rfl
  have hfQ : (Over.forget Ub).IsHomLift Q₁.f fQ := IsHomLift.of_fac' _ _ _ rfl rfl (by simp [fQ])
  have hνf : (Over.forget Ub).IsHomLift (Q₂.f ≫ b.aV) (ν ≫ fQ) := by
    rw [b.wf]
    exact @IsHomLift.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hν' hfQ
  obtain ⟨αU, hαU, hαUf⟩ := exists_fill hO rfl cx hcx (ν ≫ fQ) hνf
  let tU : SquareSpan (Over.forget Ub) Q₂.f Q₂.g := ⟨z, xU, u', αU, μ, hαU, hμ'⟩
  -- the comparison morphisms into `s₁`
  let χx : F.obj xU ⟶ s₁.x := F.map cx ≫ ιY
  let χu : F.obj z ⟶ s₁.u := F.map ν ≫ θ
  have hχx : 𝒳.val.val.p.IsHomLift b.aV χx :=
    isHomLift_comp_id_right_explicit _ _ _ (isHomLift_map_explicit hF b.aV cx hcx) hιY
  have hχu : 𝒳.val.val.p.IsHomLift b.aU χu :=
    isHomLift_comp_id_right_explicit _ _ _ (isHomLift_map_explicit hF b.aU ν hν') hθl
  obtain ⟨mx, hmxl, hmx⟩ := exists_fill hp (g := 𝟙 _) (Category.id_comp _).symm
    χx hχx m₂.mx m₂.isHomLift_mx
  obtain ⟨mu, hmul, hmu⟩ := exists_fill hp (g := 𝟙 _) (Category.id_comp _).symm
    χu hχu m₂.mu m₂.isHomLift_mu
  obtain ⟨my, hmyl, hmy⟩ := exists_fill hp (g := 𝟙 _) (Category.id_comp _).symm
    ψ hψ m₂.my m₂.isHomLift_my
  have hFα : 𝒳.val.val.p.IsHomLift Q₂.f (F.map αU) := isHomLift_map_explicit hF Q₂.f αU hαU
  have hFμ : 𝒳.val.val.p.IsHomLift Q₂.g (F.map μ) := isHomLift_map_explicit hF Q₂.g μ hμ'
  refine nonempty_cocone_of_hom_map hF hp Q₂ hpush₂ s₂ tU
    ⟨mu, mx, my, hmul, hmxl, hmyl, ?_, ?_⟩
  · refine hom_ext_explicit hp Q₂.f χx hχx
      (isHomLift_comp_id_right_explicit _ _ _ s₂.isHomLift_α hmxl)
      (isHomLift_comp_id_left_explicit _ _ _ hmul hFα) ?_
    show (s₂.α ≫ mx) ≫ χx = (mu ≫ F.map αU) ≫ χx
    calc (s₂.α ≫ mx) ≫ χx = s₂.α ≫ m₂.mx := by rw [Category.assoc, hmx]
      _ = m₂.mu ≫ s₁.α := m₂.comm_α
      _ = mu ≫ F.map ν ≫ θ ≫ s₁.α := by rw [← hmu]; simp only [χu, Category.assoc]
      _ = mu ≫ F.map ν ≫ F.map fQ ≫ ιY := by rw [hθ]
      _ = mu ≫ (F.map ν ≫ F.map fQ) ≫ ιY := by simp only [Category.assoc]
      _ = mu ≫ F.map (ν ≫ fQ) ≫ ιY :=
          congrArg (fun t => mu ≫ t ≫ ιY) (F.map_comp ν fQ).symm
      _ = mu ≫ F.map (αU ≫ cx) ≫ ιY := congrArg (fun t => mu ≫ F.map t ≫ ιY) hαUf.symm
      _ = mu ≫ (F.map αU ≫ F.map cx) ≫ ιY :=
          congrArg (fun t => mu ≫ t ≫ ιY) (F.map_comp αU cx)
      _ = (mu ≫ F.map αU) ≫ χx := by simp only [χx, Category.assoc]
  · refine hom_ext_explicit hp Q₂.g ψ hψ
      (isHomLift_comp_id_right_explicit _ _ _ s₂.isHomLift_β hmyl)
      (isHomLift_comp_id_left_explicit _ _ _ hmul hFμ) ?_
    show (s₂.β ≫ my) ≫ ψ = (mu ≫ F.map μ) ≫ ψ
    calc (s₂.β ≫ my) ≫ ψ = s₂.β ≫ m₂.my := by rw [Category.assoc, hmy]
      _ = m₂.mu ≫ s₁.β := m₂.comm_β
      _ = mu ≫ F.map ν ≫ θ ≫ s₁.β := by rw [← hmu]; simp only [χu, Category.assoc]
      _ = mu ≫ F.map μ ≫ ψ := by rw [hcomp]
      _ = (mu ≫ F.map μ) ≫ ψ := (Category.assoc _ _ _).symm

end Local

/-! ### Essential surjectivity -/

section Main

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- The underlying space of an affine scheme with Artinian local ring of global sections has a
single point. -/
theorem subsingleton_of_isArtinianRing (T : Scheme.{u}) [IsAffine T] [IsLocalRing Γ(T, ⊤)]
    [IsArtinianRing Γ(T, ⊤)] : Subsingleton T := by
  have : Subsingleton (Spec Γ(T, ⊤)) := Ring.KrullDimLE.subsingleton_primeSpectrum Γ(T, ⊤)
  exact ⟨fun a b => T.isoSpec.hom.homeomorph.injective (Subsingleton.elim _ _)⟩

/-- A surjective morphism out of a scheme with a single point has a target with a single
point. -/
theorem subsingleton_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    [Subsingleton X] : Subsingleton Y := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := f.surjective a
  obtain ⟨b', rfl⟩ := f.surjective b
  rw [Subsingleton.elim a' b']


/-- A morphism from a nonempty scheme to a scheme with a single point is surjective. -/
private theorem surjective_of_nonempty_of_subsingleton {X Y : Scheme.{u}} (f : X ⟶ Y) [Nonempty X]
    [Subsingleton Y] : Surjective f :=
  ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩

/-- A closed immersion from a nonempty scheme to a scheme with a single point is a
thickening. -/
private theorem isThickening_of_isClosedImmersion_of_subsingleton {T T' : Scheme.{u}} (i : T ⟶ T')
    (hi : IsClosedImmersion i) [Nonempty T] [Subsingleton T'] : Stacks.Thickenings.IsThickening i :=
  ⟨hi, fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩

/-- Fibre products of affine objects of the site are affine. -/
theorem isAffine_pullback {A A' C : BigFppfOver B S hS} (f : A ⟶ C) (g : A' ⟶ C)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj A)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj A')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj C)] :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback f g)) :=
  IsAffine.of_isPullback ((IsPullback.of_hasPullback f g).map (BigFppfOver.toScheme B S hS))

/-- Base change in the site preserves étale morphisms. -/
theorem etale_pullback_fst {A A' C : BigFppfOver B S hS} (f : A ⟶ C) (g : A' ⟶ C)
    [Etale ((BigFppfOver.toScheme B S hS).map g)] :
    Etale ((BigFppfOver.toScheme B S hS).map (pullback.fst f g)) :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback f g).map
    (BigFppfOver.toScheme B S hS)).flip ‹_›

/-- Base change in the site preserves étale morphisms, second projection. -/
theorem etale_pullback_snd {A A' C : BigFppfOver B S hS} (f : A ⟶ C) (g : A' ⟶ C)
    [Etale ((BigFppfOver.toScheme B S hS).map f)] :
    Etale ((BigFppfOver.toScheme B S hS).map (pullback.snd f g)) :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback f g).map
    (BigFppfOver.toScheme B S hS)) ‹_›

/-- If `c` is surjective and its base change `c'` along `τ` sits over a surjection `e`, then `τ`
is surjective. -/
theorem surjective_of_isPullback_of_surjective {P A Z' Z : Scheme.{u}} {e : P ⟶ A} {c' : P ⟶ Z'}
    {c : A ⟶ Z} {τ : Z' ⟶ Z} (h : IsPullback e c' c τ) [Surjective c] [Surjective e] :
    Surjective τ := by
  refine ⟨fun z => ?_⟩
  obtain ⟨x, rfl⟩ := c.surjective z
  obtain ⟨y, rfl⟩ := e.surjective x
  refine ⟨c' y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]

/-- **Cocones over a span are unique at the overlaps of an étale base change of a thickening
square.** -/
theorem hasUniqueSquareCocones_overlaps (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hdiag : Stack.HasRepresentableDiagonal B S hS 𝒳.val) (Q : BaseSquare (BigFppfOver B S hS))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.W)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.Z)]
    (hΓ : IsPullback ((BigFppfOver.toScheme B S hS).map Q.i).appTop
      ((BigFppfOver.toScheme B S hS).map Q.j).appTop
      ((BigFppfOver.toScheme B S hS).map Q.f).appTop
      ((BigFppfOver.toScheme B S hS).map Q.g).appTop)
    (hg : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map Q.g))
    {Z' : BigFppfOver B S hS} (τ : Z' ⟶ Q.Z) [IsAffine ((BigFppfOver.toScheme B S hS).obj Z')]
    [Etale ((BigFppfOver.toScheme B S hS).map τ)] :
    (∀ _k _l : PUnit.{w + 1}, HasUniqueSquareCocones 𝒳.val.val.p
      (Q.baseChange (pullback.fst τ τ ≫ τ)).f (Q.baseChange (pullback.fst τ τ ≫ τ)).g
      (Q.baseChange (pullback.fst τ τ ≫ τ)).i (Q.baseChange (pullback.fst τ τ ≫ τ)).j) ∧
    (∀ _k _l _m : PUnit.{w + 1}, HasUniqueSquareCocones 𝒳.val.val.p
      (Q.baseChange (pullback.fst (pullback.snd τ τ) (pullback.fst τ τ) ≫ pullback.fst τ τ ≫ τ)).f
      (Q.baseChange (pullback.fst (pullback.snd τ τ) (pullback.fst τ τ) ≫ pullback.fst τ τ ≫ τ)).g
      (Q.baseChange (pullback.fst (pullback.snd τ τ) (pullback.fst τ τ) ≫ pullback.fst τ τ ≫ τ)).i
      (Q.baseChange (pullback.fst (pullback.snd τ τ) (pullback.fst τ τ) ≫ pullback.fst τ τ ≫ τ)).j)
    := by
  let toS := BigFppfOver.toScheme B S hS
  have := isAffine_pullback B S hS τ τ
  have := etale_pullback_fst B S hS τ τ
  have := etale_pullback_snd B S hS τ τ
  have := isAffine_pullback B S hS (pullback.snd τ τ) (pullback.fst τ τ)
  have := etale_pullback_fst B S hS (pullback.snd τ τ) (pullback.fst τ τ)
  have : Etale (toS.map (pullback.fst τ τ ≫ τ)) := by
    rw [toS.map_comp]
    infer_instance
  have : Etale (toS.map (pullback.fst (pullback.snd τ τ) (pullback.fst τ τ) ≫
      pullback.fst τ τ ≫ τ)) := by
    rw [toS.map_comp, toS.map_comp]
    infer_instance
  exact ⟨fun _ _ => hasUniqueSquareCocones_baseChange_of_flat B S hS 𝒳.val hdiag Q hΓ hg _,
    fun _ _ _ => hasUniqueSquareCocones_baseChange_of_flat B S hS 𝒳.val hdiag Q hΓ hg _⟩

/-- **Algebraic stacks satisfy (RS) at squares inducing isomorphisms on residue fields: the
essential surjectivity.** Let `X ⟶ X'` be a closed immersion and `Y' = Y ⨿_X X'` a pushout of
schemes over `S` whose four corners are spectra of Artinian local rings, such that `Γ(Y) ⟶ Γ(X)`
induces a surjection onto the residue field of `Γ(X)`. Then for an algebraic stack `𝒳` the
comparison functor `𝒳_{Y'} ⟶ 𝒳_Y ×_{𝒳_X} 𝒳_{X'}` is essentially surjective. -/
theorem essSurj_fiberSquareComparison_of_residueField (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (j : X ⟶ Y) (i' : X' ⟶ Y') (j' : Y ⟶ Y')
    (w : i ≫ i' = j ≫ j')
    [IsAffine ((BigFppfOver.toScheme B S hS).obj X)]
    [IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)]
    [IsArtinianRing Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj X')]
    [IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj X', ⊤)]
    [IsArtinianRing Γ((BigFppfOver.toScheme B S hS).obj X', ⊤)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]
    [IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)]
    [IsArtinianRing Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Y')]
    [IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj Y', ⊤)]
    [IsArtinianRing Γ((BigFppfOver.toScheme B S hS).obj Y', ⊤)]
    (hi : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hpo : IsPushout ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map j)
      ((BigFppfOver.toScheme B S hS).map i') ((BigFppfOver.toScheme B S hS).map j'))
    (hres : Function.Surjective
      ((IsLocalRing.residue Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)).comp
        ((BigFppfOver.toScheme B S hS).map j).appTop.hom)) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    (fiberSquareComparison 𝒳.val.val.p 𝒳.val.val.p.chosenPullbacks j i j' i' w.symm).EssSurj := by
  classical
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let toS := BigFppfOver.toScheme B S hS
  have hp := 𝒳.val.isFiberedInGroupoids
  have hst : 𝒳.val.val.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS) :=
    Stack.isStackInGroupoids_of_isAlgebraicStack B S hS 𝒳.property
  have hdiag : Stack.HasRepresentableDiagonal B S hS 𝒳.val :=
    Stack.SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack B S hS 𝒳.val 𝒳.property
  obtain ⟨Ub, a, hasm, hasurj⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  let F := CatFiberedInGroupoids.homFunctor a.hom
  have := hi
  apply essSurj_fiberSquareComparison_of_nonempty_cocone hp _ j i j' i' w.symm
  intro s
  let Q : BaseSquare (BigFppfOver B S hS) := ⟨X, Y, X', Y', j, i, j', i', w.symm⟩
  -- facts about the square
  have hΓ : IsPullback (toS.map j').appTop (toS.map i').appTop (toS.map j).appTop
      (toS.map i).appTop := isPullback_appTop_of_isPushout hpo
  have hisurj : Function.Surjective (toS.map i).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine _).2
  have hj'surj : Function.Surjective (toS.map j').appTop.hom := surjective_of_isPullback hΓ hisurj
  -- the closed point
  let κ := IsLocalRing.ResidueField Γ(toS.obj X, ⊤)
  let φX : Γ(toS.obj X, ⊤) ⟶ CommRingCat.of κ :=
    CommRingCat.ofHom (IsLocalRing.residue Γ(toS.obj X, ⊤))
  let pX : Spec (.of κ) ⟶ toS.obj X := Spec.map φX ≫ (toS.obj X).isoSpec.inv
  have hpXapp : pX.appTop = φX ≫ (Scheme.ΓSpecIso (.of κ)).inv :=
    appTop_specMap_comp_isoSpec_inv φX
  have hsurjΓ : ∀ {T : Scheme.{u}} (g : toS.obj X ⟶ T),
      Function.Surjective (φX.hom.comp g.appTop.hom) → Function.Surjective (pX ≫ g).appTop.hom := by
    intro T g hg
    rw [Scheme.Hom.comp_appTop, hpXapp, CommRingCat.hom_comp, CommRingCat.hom_comp]
    exact (Scheme.ΓSpecIso (.of κ)).commRingCatIsoToRingEquiv.symm.surjective.comp hg
  have : Nonempty (Spec (.of κ)) := ⟨IsLocalRing.closedPoint κ⟩
  have : Nonempty (toS.obj X) := ⟨pX (IsLocalRing.closedPoint κ)⟩
  have : IsClosedImmersion pX := by
    have : IsClosedImmersion (Spec.map φX) :=
      IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
    infer_instance
  have hpY : IsClosedImmersion (pX ≫ toS.map j) :=
    IsClosedImmersion.of_surjective_of_isAffine _ (hsurjΓ _ hres)
  have hcY' : IsClosedImmersion ((pX ≫ toS.map j) ≫ toS.map j') := by
    refine IsClosedImmersion.of_surjective_of_isAffine _ ?_
    rw [Category.assoc]
    refine hsurjΓ _ ?_
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, ← RingHom.comp_assoc]
    exact hres.comp hj'surj
  have := hpY
  have := hcY'
  have hpYFO : Stacks.Thickenings.IsFiniteOrderThickening (pX ≫ toS.map j) :=
    isFiniteOrderThickening_of_isClosedImmersion _
  have hpXFO : Stacks.Thickenings.IsFiniteOrderThickening pX :=
    isFiniteOrderThickening_of_isClosedImmersion _
  have hiFO : Stacks.Thickenings.IsFiniteOrderThickening (toS.map i) :=
    isFiniteOrderThickening_of_isClosedImmersion _
  have : Subsingleton (toS.obj X') := subsingleton_of_isArtinianRing _
  have : Subsingleton (toS.obj Y') := subsingleton_of_isArtinianRing _
  have hithick := isThickening_of_isClosedImmersion_of_subsingleton (toS.map i) hi
  -- step 1: lift `s.x` to the presentation after a smooth base change, then after an étale
  -- neighbourhood of the closed point of `Y'`
  obtain ⟨T₀, m₀, hm₀sm, hm₀surj, xc, αc, hαc⟩ :=
    Stack.exists_scheme_lift_of_isSurjective_isSmooth B S hS a hasurj hasm Y
      (Functor.Fiber.mk (IsHomLift.codomain_eq 𝒳.val.val.p j s.α))
  let TY : BigFppfOver B S hS := Over.mk (m₀ ≫ Y.hom)
  let mY : TY ⟶ Y := Over.homMk m₀ rfl
  obtain ⟨K₁, _, Z₁, τ₁, c₁, e₁, -, hZ₁, hτ₁, hpb₁, r₁, hr₁⟩ :=
    exists_etale_section_of_smooth_of_closedPoint_site B S hS (Z := Y') (T := Y) (T₀ := TY) j' mY
      hm₀sm hm₀surj ((pX ≫ toS.map j) ≫ toS.map j') (pX ≫ toS.map j) hpYFO rfl
  have := hZ₁
  have := hτ₁
  have : IsClosedImmersion c₁ := MorphismProperty.of_isPullback hpb₁ hcY'
  have : Nonempty (Spec (.of K₁)) := ⟨IsLocalRing.closedPoint K₁⟩
  have : Subsingleton (Spec (.of K₁)) := Ring.KrullDimLE.subsingleton_primeSpectrum K₁
  have : Surjective ((pX ≫ toS.map j) ≫ toS.map j') :=
    surjective_of_nonempty_of_subsingleton _
  have : Surjective c₁ := MorphismProperty.of_isPullback hpb₁ ‹_›
  have : Subsingleton (toS.obj Z₁) := subsingleton_of_surjective c₁
  have : Nonempty (toS.obj Z₁) := ⟨c₁ (IsLocalRing.closedPoint K₁)⟩
  have : Surjective (toS.map τ₁) := surjective_of_nonempty_of_subsingleton _
  -- facts about `Q` and its base change along `τ₁`
  have : IsAffine (toS.obj Q.U) := ‹IsAffine (toS.obj X)›
  have : IsAffine (toS.obj Q.V) := ‹IsAffine (toS.obj Y)›
  have : IsAffine (toS.obj Q.W) := ‹IsAffine (toS.obj X')›
  have : IsAffine (toS.obj Q.Z) := ‹IsAffine (toS.obj Y')›
  obtain ⟨hU₁, hV₁, hW₁, hΓ₁, hg₁, hpush₁⟩ := baseChange_facts B S hS Q hΓ hiFO τ₁
  have := hU₁
  have := hV₁
  have := hW₁
  obtain ⟨huniq₂, huniq₃⟩ := hasUniqueSquareCocones_overlaps B S hS 𝒳 hdiag Q hΓ hithick τ₁
  refine hst.nonempty_cocone_of_baseChange Q (I := PUnit.{w + 1}) (fun _ => τ₁)
    (singleton_mem_topology B S hS τ₁ inferInstance inferInstance inferInstance) s ?_
    huniq₂ huniq₃
  intro _ s₁ m₁
  let Q₁ := Q.baseChange τ₁
  have hF : F ⋙ 𝒳.val.val.p = Over.forget Ub := CatFiberedInGroupoids.homFunctor_comp_p a.hom
  -- the lift of `s₁.x` to the presentation
  have hαc' : 𝒳.val.val.p.IsHomLift mY αc := hαc
  have hxc : xc.left = TY := by
    have h1 : 𝒳.val.val.p.obj (F.obj xc) = TY := IsHomLift.domain_eq _ mY αc
    rw [← h1]
    exact (congrArg (fun G => G.obj xc) hF).symm
  let yv : Q₁.V ⟶ Ub := r₁ ≫ eqToHom hxc.symm ≫ xc.hom
  let κY : (Over.mk yv : Over Ub) ⟶ xc := Over.homMk (r₁ ≫ eqToHom hxc.symm) (by simp [yv])
  have hκY : (Over.forget Ub).IsHomLift r₁ κY := by
    apply IsHomLift.of_fac' _ _ _ rfl hxc
    simp only [eqToHom_refl, Category.id_comp]
    rfl
  have hFκ : 𝒳.val.val.p.IsHomLift r₁ (F.map κY) := isHomLift_map_explicit hF r₁ κY hκY
  have hφ' : 𝒳.val.val.p.IsHomLift (Q.baseChangeHom τ₁).aV (F.map κY ≫ αc) := by
    have h := @IsHomLift.comp _ _ _ _ _ _ _ _ _ _ _ r₁ mY (F.map κY) αc hFκ hαc'
    rw [hr₁] at h
    exact h
  obtain ⟨ιY, hιY, hιYf⟩ := exists_fill hp (g := 𝟙 _) (Category.id_comp _).symm m₁.mx
    m₁.isHomLift_mx (F.map κY ≫ αc) hφ'
  have := hιY
  -- the lift of `s₁.u`
  let fQ : (Over.mk (Q₁.f ≫ yv) : Over Ub) ⟶ Over.mk yv := Over.homMk Q₁.f rfl
  have hfQ : (Over.forget Ub).IsHomLift Q₁.f fQ := IsHomLift.of_fac' _ _ _ rfl rfl (by simp [fQ])
  have hθφ : 𝒳.val.val.p.IsHomLift Q₁.f (F.map fQ ≫ ιY) :=
    isHomLift_comp_id_right_explicit _ _ _ (isHomLift_map_explicit hF _ fQ hfQ) hιY
  obtain ⟨θ, hθl, hθ⟩ := exists_fill hp (g := 𝟙 _) (Category.id_comp _).symm s₁.α
    s₁.isHomLift_α (F.map fQ ≫ ιY) hθφ
  have := hθl
  -- step 2: extend across the thickening, then an étale neighbourhood of the closed point
  have hα₁ : 𝒳.val.val.p.IsHomLift Q₁.g (θ ≫ s₁.β) :=
    isHomLift_comp_id_left_explicit _ _ _ hθl s₁.isHomLift_β
  obtain ⟨Tc, mX, hmXsm, hmXsurj, hext⟩ :=
    Stack.exists_smooth_extension_of_isFiniteOrderThickening B S hS a hasurj hasm Q₁.g s₁.y
      (Over.mk (Q₁.f ≫ yv)) (θ ≫ s₁.β) hα₁
  obtain ⟨p₁, hp₁FO, hp₁snd, -⟩ := exists_closedPoint_pullback B S hS (Q.f ≫ Q.i) τ₁ _ c₁ e₁
    hpb₁ pX hpXFO (by
      show pX ≫ toS.map (j ≫ j') = (pX ≫ toS.map j) ≫ toS.map j'
      rw [toS.map_comp, ← Category.assoc])
  have hpt₁ : p₁ ≫ toS.map (Q₁.f ≫ Q₁.i) = c₁ := by
    have : Q₁.f ≫ Q₁.i = pullback.snd (Q.f ≫ Q.i) τ₁ := pullback.lift_snd _ _ _
    rw [this]
    exact hp₁snd
  obtain ⟨K₂, _, Z₂, τ₂, c₂, e₂, -, hZ₂, hτ₂, hpb₂, rX, hrX⟩ :=
    exists_etale_section_of_smooth_of_closedPoint_site B S hS (Z := Z₁) (T := Q₁.U) (T₀ := Tc)
      (Q₁.f ≫ Q₁.i) mX hmXsm hmXsurj c₁ p₁ hp₁FO hpt₁
  have := hZ₂
  have := hτ₂
  have : Nonempty (Spec (.of K₂)) := ⟨IsLocalRing.closedPoint K₂⟩
  have : Nonempty (toS.obj Z₂) := ⟨c₂ (IsLocalRing.closedPoint K₂)⟩
  have : Surjective (toS.map τ₂) := surjective_of_nonempty_of_subsingleton _
  have : IsAffine (toS.obj Q₁.Z) := ‹IsAffine (toS.obj Z₁)›
  obtain ⟨hU₂, -, hW₂, -, hg₂, hpush₂⟩ := baseChange_facts B S hS Q₁ hΓ₁ hg₁ τ₂
  obtain ⟨huniq₂', huniq₃'⟩ :=
    hasUniqueSquareCocones_overlaps B S hS 𝒳 hdiag Q₁ hΓ₁ hg₁.isThickening τ₂
  refine hst.nonempty_cocone_of_baseChange Q₁ (I := PUnit.{w + 1}) (fun _ => τ₂)
    (singleton_mem_topology B S hS τ₂ inferInstance inferInstance inferInstance) s₁ ?_
    huniq₂' huniq₃'
  intro _ s₂ m₂
  exact nonempty_cocone_of_extension B S hS 𝒳 a Q₁ s₁ yv ιY θ hθ mX hext τ₂ rX hrX hU₂ hW₂
    hg₂ hpush₂ s₂ m₂


/-- The comparison functors of condition (RS) are fully faithful for an algebraic stack. -/
private theorem satisfiesRSFullyFaithful_aux (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    SatisfiesRSFullyFaithful B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids := by
  intro X X' Y Y' i j i' j' w hX hX' hY hY' _ _ _ _ hi hpo
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  obtain ⟨hXa, hXl, hXr⟩ := hX
  obtain ⟨hX'a, hX'l, hX'r⟩ := hX'
  obtain ⟨hYa, -, -⟩ := hY
  let toS := BigFppfOver.toScheme B S hS
  have hdiag : Stack.HasRepresentableDiagonal B S hS 𝒳.val :=
    Stack.SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack B S hS 𝒳.val 𝒳.property
  have : Subsingleton (toS.obj X') := subsingleton_of_isArtinianRing _
  have : Nonempty (toS.obj X) := ⟨(toS.obj X).isoSpec.inv (IsLocalRing.closedPoint _)⟩
  have hFF := fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal B S hS 𝒳.val hdiag
    i j i' j' w (isThickening_of_isClosedImmersion_of_subsingleton (toS.map i) hi) hpo
  exact ⟨hFF.full, hFF.faithful⟩

/-- **Algebraic stacks satisfy condition (RS) at the squares inducing surjections of residue
fields.** Full faithfulness of the comparison holds for any category fibred in groupoids with
representable diagonal, and essential surjectivity is
`Deformation.Artin.essSurj_fiberSquareComparison_of_residueField`. -/
theorem satisfiesRSOfResidue_of_isAlgebraicStack (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    SatisfiesRSOfResidue B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids := by
  intro X X' Y Y' i j i' j' w hX hX' hY hY' h₁ h₂ h₃ h₄ hi hpo hres
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have hFF := satisfiesRSFullyFaithful_aux B S hS 𝒳 i j i' j' w hX hX' hY hY' h₁ h₂ h₃ h₄ hi hpo
  have := hFF.1
  have := hFF.2
  obtain ⟨hXa, hXl, hXr⟩ := hX
  obtain ⟨hX'a, hX'l, hX'r⟩ := hX'
  obtain ⟨hYa, hYl, hYr⟩ := hY
  obtain ⟨hY'a, hY'l, hY'r⟩ := hY'
  let toS := BigFppfOver.toScheme B S hS
  have hres' : Function.Surjective ((IsLocalRing.residue Γ(toS.obj X, ⊤)).comp
      (toS.map j).appTop.hom) := by
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨b, hb⟩ := hres a
    refine ⟨b, ?_⟩
    rw [RingHom.comp_apply, eq_comm, ← sub_eq_zero, ← _root_.map_sub,
      IsLocalRing.residue_eq_zero_iff]
    exact hb
  have := essSurj_fiberSquareComparison_of_residueField B S hS 𝒳 i j i' j' w hi hpo hres'
  exact { }

/-- **The predeformation category of a point of an algebraic stack is a deformation
category.** -/
theorem isDeformationCategory_predeformationCategory_of_isAlgebraicStack
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : 𝒳.val.val.obj)
    (hx₀ : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let D := predeformationCategory iΛ (𝒳.val.val.p ⋙ Over.post B.inclusion) x₀ hx₀
    letI := D.category
    Deformation.IsDeformationCategory D.projection :=
  isDeformationCategory_predeformationCategory_of_satisfiesRSOfResidue B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (satisfiesRSOfResidue_of_isAlgebraicStack B S hS 𝒳) iΛ x₀ hx₀
    hfinite hqc


/-- **The comparison functors of condition (RS) are fully faithful for an algebraic stack.** -/
theorem satisfiesRSFullyFaithful_of_isAlgebraicStack (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    SatisfiesRSFullyFaithful B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids :=
  satisfiesRSFullyFaithful_aux B S hS 𝒳

end Main

end Deformation.Artin

end
