module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer

/-!
# Monomorphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism of formal algebraic spaces
over `S` is a morphism of the underlying fppf sheaves, and it is a *monomorphism*
(Stacks 0AQB) when it is an injective map of sheaves, which is Mathlib's
`CategoryTheory.Mono` for the category `AlgebraicGeometry.FormalSpace.FppfSheaf` of those
sheaves. The two soriteses of the source, stability under composition and under base change,
are therefore its general categorical counterparts, instantiated here at that category.

Monomorphy can also be tested on base changes: it is equivalent to monomorphy of every base
change along a scheme over `S` in the site mapping to the target, to the same for the affine
such schemes alone, to monomorphy of the base changes along the members of an atlas of the
target as in Stacks 0AIM, and to the same along any family of morphisms onto the target whose
induced map from the coproduct is a surjection of sheaves.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsMonoOnSchemeBaseChanges`,
  `AlgebraicGeometry.FormalSpace.IsMonoOnAffineBaseChanges`,
  `AlgebraicGeometry.FormalSpace.HasMonoFormalAtlas`,
  `AlgebraicGeometry.FormalSpace.HasMonoLocallySurjectiveFamily`: conditions (2), (3), (4)
  and (5) of **Stacks 0GHV**.

## Main results

* `AlgebraicGeometry.FormalSpace.mono_comp`: **Stacks 0GHT**, the composition of two
  monomorphisms is a monomorphism.
* `AlgebraicGeometry.FormalSpace.Mono.of_isPullback`: **Stacks 0GHU**, a base change of a
  monomorphism is a monomorphism.
* `AlgebraicGeometry.FormalSpace.mono_tfae`: **Stacks 0GHV** for its conditions (1), (2), (3),
  (4) and (5).
* `AlgebraicGeometry.FormalSpace.mono_tfae'`: the same for its conditions (1), (2), (3) and
  (5), with no hypothesis on the target.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AQB](https://stacks.math.columbia.edu/tag/0AQB)
* [Stacks Project, Tag 0GHT](https://stacks.math.columbia.edu/tag/0GHT)
* [Stacks Project, Tag 0GHU](https://stacks.math.columbia.edu/tag/0GHU)
* [Stacks Project, Tag 0GHV](https://stacks.math.columbia.edu/tag/0GHV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two soriteses -/

/-- The composition of two monomorphisms of formal algebraic spaces over `S` is a
monomorphism. -/
@[stacks 0GHT]
theorem mono_comp {X Y Z : FppfSheaf B S hS} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Mono f) (hg : Mono g) : Mono (f ≫ g) :=
  CategoryTheory.mono_comp' hf hg

/-- A base change of a monomorphism of formal algebraic spaces over `S` is a monomorphism: in
the cartesian square with `f` on the right and `p` on the left, if `f` is a monomorphism then so
is `p`. -/
@[stacks 0GHU]
theorem Mono.of_isPullback {W X Z Y : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hf : Mono f) : Mono p :=
  sq.mono_fst_of_mono hf

/-! ### The conditions of Stacks 0GHV -/

/-- **Stacks 0GHV, condition (2).** Every base change of a morphism of fppf sheaves on the big
fppf site of `S` along a scheme over `S` in the site mapping to its target is a
monomorphism. -/
abbrev IsMonoOnSchemeBaseChanges {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (T : BigFppfOver B S hS) (g : yonedaSheaf B S hS T ⟶ Y) (W : FppfSheaf B S hS)
    (p : W ⟶ yonedaSheaf B S hS T) (q : W ⟶ X), IsPullback p q g f → Mono p

/-- **Stacks 0GHV, condition (3).** Every base change of a morphism of fppf sheaves on the big
fppf site of `S` along an affine scheme over `S` in the site mapping to its target is a
monomorphism. -/
abbrev IsMonoOnAffineBaseChanges {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
    ∀ (g : yonedaSheaf B S hS T ⟶ Y) (W : FppfSheaf B S hS)
      (p : W ⟶ yonedaSheaf B S hS T) (q : W ⟶ X), IsPullback p q g f → Mono p

/-- **Stacks 0GHV, condition (4).** There is a covering of the target of a morphism of fppf
sheaves on the big fppf site of `S` as in Definition 0AIM — by affine formal algebraic spaces,
along morphisms representable by algebraic spaces and étale, jointly surjective as a map of
sheaves — each of whose base changes of the morphism is a monomorphism. -/
abbrev HasMonoFormalAtlas {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  ∃ (I : Type (u + 1)) (Yi : I → FppfSheaf B S hS) (c : ∀ i, Yi i ⟶ Y),
    (∀ i, IsAffineFormalAlgebraicSpace B S hS (Yi i)) ∧
    (∀ i, ∃ hci : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (c i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (c i).hom hci) ∧
    Sheaf.IsLocallySurjective (Sigma.desc c) ∧
    ∀ (i : I) (W : FppfSheaf B S hS) (p : W ⟶ Yi i) (q : W ⟶ X),
      IsPullback p q (c i) f → Mono p

/-- **Stacks 0GHV, condition (5).** There is a family of morphisms onto the target of a
morphism of fppf sheaves on the big fppf site of `S` whose induced map from the coproduct is a
surjection of sheaves, each of whose base changes of the morphism is a monomorphism. -/
abbrev HasMonoLocallySurjectiveFamily {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  ∃ (I : Type (u + 1)) (Yi : I → FppfSheaf B S hS) (c : ∀ i, Yi i ⟶ Y),
    Sheaf.IsLocallySurjective (Sigma.desc c) ∧
    ∀ (i : I) (W : FppfSheaf B S hS) (p : W ⟶ Yi i) (q : W ⟶ X),
      IsPullback p q (c i) f → Mono p

/-! ### The criteria -/

/-- A section of an fppf sheaf `X` over an object `T` of the big fppf site of `S`, read as a
morphism into `X` from the sheaf represented by `T`, by Yoneda's lemma for the universe-lifted
Yoneda presheaf. -/
private def yonedaSection {X : FppfSheaf B S hS} {T : BigFppfOver B S hS}
    (x : X.obj.obj (op T)) : yonedaSheaf B S hS T ⟶ X :=
  ⟨uliftYonedaEquiv.{u + 1}.symm x⟩

/-- Composing the morphism of a section with a morphism of fppf sheaves gives the morphism of
the image of that section. -/
private theorem yonedaSection_comp {X Y : FppfSheaf B S hS} {T : BigFppfOver B S hS}
    (x : X.obj.obj (op T)) (f : X ⟶ Y) :
    yonedaSection B S hS x ≫ f = yonedaSection B S hS (f.hom.app (op T) x) :=
  Sheaf.hom_ext (uliftYonedaEquiv_symm_comp x f.hom)

/-- Distinct sections give distinct morphisms. -/
private theorem yonedaSection_injective {X : FppfSheaf B S hS} {T : BigFppfOver B S hS}
    {x y : X.obj.obj (op T)} (h : yonedaSection B S hS x = yonedaSection B S hS y) : x = y :=
  uliftYonedaEquiv.{u + 1}.symm.injective
    (congrArg (fun m : yonedaSheaf B S hS T ⟶ X ↦ m.hom) h)

/-- Two morphisms into the source of `f : X ⟶ Y` whose composites with `f` are one and the same
factorisation `γ ≫ g` agree, provided the second projection of the fibre product of `f` along
`g` is a monomorphism. -/
private theorem eq_of_mono_pullback_snd {W X Y Z : FppfSheaf B S hS} {f : X ⟶ Y} {g : Z ⟶ Y}
    (hmono : Mono (pullback.snd f g)) {a b : W ⟶ X} {γ : W ⟶ Z}
    (ha : a ≫ f = γ ≫ g) (hb : b ≫ f = γ ≫ g) : a = b := by
  have heq : pullback.lift a γ ha = pullback.lift b γ hb :=
    (cancel_mono (pullback.snd f g)).1 (by rw [pullback.lift_snd, pullback.lift_snd])
  simpa only [pullback.lift_fst] using heq =≫ pullback.fst f g

/-- Two sections of `X` over an object `T` of the big fppf site of `S` agree when their
morphisms out of the sheaf represented by `T` compose with `f` to one and the same
factorisation through a `g` whose base change of `f` is a monomorphism. -/
private theorem eq_section_of_mono_pullback_snd {X Y Z : FppfSheaf B S hS} {f : X ⟶ Y}
    {g : Z ⟶ Y} (hmono : Mono (pullback.snd f g)) {T : BigFppfOver B S hS}
    {x y : X.obj.obj (op T)} {γ : yonedaSheaf B S hS T ⟶ Z}
    (hx : yonedaSection B S hS x ≫ f = γ ≫ g)
    (hy : yonedaSection B S hS y ≫ f = γ ≫ g) : x = y :=
  yonedaSection_injective B S hS (eq_of_mono_pullback_snd B S hS hmono hx hy)

/-- Two sections of `X` over an object `T` of the big fppf site of `S` which agree under
`f : X ⟶ Y` agree, provided every base change of `f` along a morphism from `T` to `Y` is a
monomorphism. -/
private theorem eq_section_of_mono_pullback_snd_self {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (T : BigFppfOver B S hS) (x y : X.obj.obj (op T))
    (hxy : f.hom.app (op T) x = f.hom.app (op T) y)
    (hmono : ∀ g : yonedaSheaf B S hS T ⟶ Y, Mono (pullback.snd f g)) :
    x = y := by
  refine eq_section_of_mono_pullback_snd B S hS
    (hmono (yonedaSection B S hS x ≫ f)) (γ := 𝟙 _) (Category.id_comp _).symm ?_
  rw [Category.id_comp, yonedaSection_comp, yonedaSection_comp, hxy]

/-- **Stacks 0GHV, condition (3) implies condition (1).** A morphism of fppf sheaves on the big
fppf site of `S` whose base change along every affine scheme over `S` in the site mapping to
its target is a monomorphism is itself a monomorphism. -/
theorem mono_of_isMonoOnAffineBaseChanges {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : IsMonoOnAffineBaseChanges B S hS f) : Mono f := by
  have hdense : (BigAffineFppf.inclusion B S hS).IsCoverDense
      (BigFppfOver.topology B S hS) :=
    Functor.IsDenseSubsite.isCoverDense (BigAffineFppf.topology B S hS)
      (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
  have : Sheaf.IsLocallyInjective f := by
    constructor
    intro U x y hxy
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (Functor.is_cover_of_isCoverDense (BigAffineFppf.inclusion B S hS)
        (BigFppfOver.topology B S hS) U.unop)
    rintro V a ⟨⟨Z, lift, map, fac⟩⟩
    have key : X.obj.map map.op x = X.obj.map map.op y := by
      refine eq_section_of_mono_pullback_snd_self B S hS f
        ((BigAffineFppf.inclusion B S hS).obj Z) _ _ ?_
        fun g ↦ h _ Z.property g _ _ _ (IsPullback.of_hasPullback f g).flip
      rw [NatTrans.naturality_apply f.hom map.op x, NatTrans.naturality_apply f.hom map.op y,
        hxy]
    change X.obj.map a.op x = X.obj.map a.op y
    rw [← fac, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, key]
  exact Sheaf.mono_of_isLocallyInjective f

/-- **Stacks 0GHV, condition (5) implies condition (1).** A morphism of fppf sheaves on the big
fppf site of `S` admitting a family of morphisms onto its target whose induced map from the
coproduct is a surjection of sheaves, and whose base changes of the morphism are all
monomorphisms, is itself a monomorphism. -/
@[sga "3 IV 4.5.7" "(ii) ⇒ (i)", sga "3 IV 4.5.8" "Monomorphism clause"]
theorem mono_of_hasMonoLocallySurjectiveFamily {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : HasMonoLocallySurjectiveFamily B S hS f) : Mono f := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨I, Yi, c, hsurj, hmono⟩ := h
  have : Sheaf.IsLocallyInjective f := by
    constructor
    intro U x y hxy
    obtain ⟨T, hT, hlocal⟩ :=
      (Sheaf.isLocallySurjective_sigmaDesc_iff c).1 hsurj (f.hom.app U x)
    refine (BigFppfOver.topology B S hS).superset_covering ?_ hT
    intro V a ha
    obtain ⟨i, z, hz⟩ := hlocal a ha
    have hmi : Mono (pullback.snd f (c i)) :=
      hmono i _ _ _ (IsPullback.of_hasPullback f (c i)).flip
    change X.obj.map a.op x = X.obj.map a.op y
    refine eq_section_of_mono_pullback_snd B S hS hmi
      (γ := yonedaSection B S hS z) ?_ ?_
    · rw [yonedaSection_comp, yonedaSection_comp, NatTrans.naturality_apply f.hom a.op x, hz]
    · rw [yonedaSection_comp, yonedaSection_comp, NatTrans.naturality_apply f.hom a.op y,
        ← hxy, hz]
  exact Sheaf.mono_of_isLocallyInjective f

/-- **Stacks 0GHV, condition (4) implies condition (5).** An atlas as in Definition 0AIM along
which every base change of a morphism of fppf sheaves is a monomorphism is in particular a
family whose induced map from the coproduct is a surjection of sheaves with that property. -/
theorem hasMonoLocallySurjectiveFamily_of_hasMonoFormalAtlas {X Y : FppfSheaf B S hS}
    {f : X ⟶ Y} (h : HasMonoFormalAtlas B S hS f) :
    HasMonoLocallySurjectiveFamily B S hS f := by
  obtain ⟨I, Yi, c, -, -, hsurjective, hmono⟩ := h
  exact ⟨I, Yi, c, hsurjective, hmono⟩

/-- For a morphism `f : X ⟶ Y` of formal algebraic spaces over `S`, with `Y` a formal algebraic
space, the following are equivalent:

1. `f` is a monomorphism;
2. for every scheme `T` over `S` in the site and every `T ⟶ Y` the projection
   `X ×_Y T ⟶ T` is a monomorphism;
3. the same for every affine scheme `T` over `S` in the site;
4. there is a covering `{Y_j ⟶ Y}` as in Definition 0AIM such that each `X ×_Y Y_j ⟶ Y_j` is a
   monomorphism;
5. there is a family `{Y_j ⟶ Y}` with `∐ Y_j ⟶ Y` a surjection of sheaves such that each
   `X ×_Y Y_j ⟶ Y_j` is a monomorphism. -/
@[stacks 0GHV "conditions (1), (2), (3), (4) and (5)"]
theorem mono_tfae {X Y : FppfSheaf B S hS} (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE
      [Mono f,
        IsMonoOnSchemeBaseChanges B S hS f,
        IsMonoOnAffineBaseChanges B S hS f,
        HasMonoFormalAtlas B S hS f,
        HasMonoLocallySurjectiveFamily B S hS f] := by
  tfae_have 1 → 2 := fun hf _ _ _ _ _ sq ↦ Mono.of_isPullback B S hS sq hf
  tfae_have 2 → 3 := fun h T _ g ↦ h T g
  tfae_have 3 → 1 := mono_of_isMonoOnAffineBaseChanges B S hS
  tfae_have 1 → 4 := by
    intro hf
    obtain ⟨-, I, Yi, c, haffine, hetale, hsurjective⟩ := hY
    exact ⟨I, Yi, c, haffine, hetale, hsurjective,
      fun _ _ _ _ sq ↦ Mono.of_isPullback B S hS sq hf⟩
  tfae_have 4 → 5 := hasMonoLocallySurjectiveFamily_of_hasMonoFormalAtlas B S hS
  tfae_have 5 → 1 := mono_of_hasMonoLocallySurjectiveFamily B S hS
  tfae_finish

/-- For an arbitrary morphism `f : X ⟶ Y` of fppf sheaves on the big fppf site of `S`,
conditions (1), (2), (3) and (5) of `AlgebraicGeometry.FormalSpace.mono_tfae` are
equivalent. -/
@[stacks 0GHV "conditions (1), (2), (3) and (5)"]
theorem mono_tfae' {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    List.TFAE
      [Mono f,
        IsMonoOnSchemeBaseChanges B S hS f,
        IsMonoOnAffineBaseChanges B S hS f,
        HasMonoLocallySurjectiveFamily B S hS f] := by
  tfae_have 1 → 2 := fun hf _ _ _ _ _ sq ↦ Mono.of_isPullback B S hS sq hf
  tfae_have 2 → 3 := fun h T _ g ↦ h T g
  tfae_have 3 → 1 := mono_of_isMonoOnAffineBaseChanges B S hS
  tfae_have 1 → 4 := by
    intro hf
    let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    refine ⟨PUnit.{u + 2}, fun _ ↦ Y, fun _ ↦ 𝟙 Y, ?_,
      fun _ _ _ _ sq ↦ Mono.of_isPullback B S hS sq hf⟩
    have hfac : (Sigma.ι (fun _ : PUnit.{u + 2} ↦ Y) PUnit.unit).hom ≫
        (Sigma.desc (fun _ : PUnit.{u + 2} ↦ (𝟙 Y : Y ⟶ Y))).hom = 𝟙 Y.obj := by
      rw [← ObjectProperty.FullSubcategory.comp_hom, Sigma.ι_desc]
      rfl
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ hfac
  tfae_have 4 → 1 := mono_of_hasMonoLocallySurjectiveFamily B S hS
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
