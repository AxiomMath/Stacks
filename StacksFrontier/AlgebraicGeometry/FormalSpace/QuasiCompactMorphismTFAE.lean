module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasFiniteSubcover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductNoetherianAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismChosenReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismDecomposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismFormalAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineDisjointUnion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalAlgebraicSpaceSanityChecks

/-!
# The four conditions of Stacks 0AJB are equivalent

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of formal
algebraic spaces over `S`. **Stacks 0AJB** says that the following are equivalent:

1. the induced morphism `f_red : X_red ⟶ Y_red` of reductions is a quasi-compact morphism of
   algebraic spaces;
2. for every quasi-compact scheme `T` and morphism `T ⟶ Y` the fibre product `X ×_Y T` is a
   quasi-compact formal algebraic space;
3. the same for every affine scheme `T`;
4. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM such that every `X ×_Y Yⱼ` is a
   quasi-compact formal algebraic space.

The implications (1) ⇒ (4), (2) ⇔ (3) and (3) ⇒ (1) are proved elsewhere in this library. This
file proves the remaining implication **(4) ⇒ (3)** and assembles the four conditions into one
`List.TFAE`.

## Main results

* `AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_of_isPullback_of_isAffineFormal`: the base
  change of a quasi-compact formal algebraic space over an affine formal algebraic space along a
  morphism from another affine formal algebraic space is a quasi-compact formal algebraic space.
* `AlgebraicGeometry.FormalSpace.HasQuasiCompactFormalAtlas.isQuasiCompact`: **Stacks 0AJB**,
  condition (4) implies condition (3).
* `AlgebraicGeometry.FormalSpace.tfae_isQuasiCompact`: **Stacks 0AJB**, the equivalence of the
  four conditions.

## The proof of (4) ⇒ (3)

Let `{cⱼ : Yⱼ ⟶ Y}` be the covering of condition (4) and let `g : T ⟶ Y` be a point with `T`
affine. Every base change `Yⱼ ×_Y T` is represented by an object `Vⱼ` of the site, étale over
`T`, by Stacks 0AIG (`AlgebraicGeometry.FormalSpace.exists_finset_pullback_cover_of_compactSpace`).
Covering each `Vⱼ` by affine opens and using that `T` is quasi-compact gives finitely many affine
objects `Uₖ` of the site, étale over `T` and covering it, each mapping to some `Yⱼ` compatibly
with `g`. The fibre product `X ×_Y T` is then covered, along the representable étale base changes
of the `Uₖ ⟶ T`, by the finitely many fibre products `X ×_Y Uₖ = (X ×_Y Yⱼ) ×_{Yⱼ} Uₖ`. Each of
these is a quasi-compact formal algebraic space: the single affine formal chart `A` of the
quasi-compact formal algebraic space `X ×_Y Yⱼ` base changes to a chart `A ×_{Yⱼ} Uₖ`, which is
an affine formal algebraic space by Stacks 0AN3 clause (1), an affine formal algebraic space being
separated. Finitely many quasi-compact pieces along representable étale morphisms assemble into
a quasi-compact formal algebraic space,
`AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_of_finite_isRepresentableEtale_cover`.

## What is assumed

Nothing. In particular the implication (1) ⇒ (3) goes through condition (4), whose members are
representable étale over `Y`, so no form of Stacks 0AJ3 or Stacks 0AIU is used.

## References

* [Stacks Project, Tag 0AIG](https://stacks.math.columbia.edu/tag/0AIG)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJB](https://stacks.math.columbia.edu/tag/0AJB)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change of a quasi-compact formal algebraic space between affine ones -/

/-- A base change of a locally surjective morphism of fppf sheaves is locally surjective. -/
private theorem isLocallySurjective_of_isPullback_of_isLocallySurjective
    {P Z Y' V : FppfSheaf B S hS} {p : P ⟶ Z} {q : P ⟶ V} {g : Z ⟶ Y'} {f : V ⟶ Y'}
    (sq : IsPullback p q g f) (hf : Sheaf.IsLocallySurjective f) :
    Sheaf.IsLocallySurjective p := by
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map f) := hf
  exact Presheaf.isLocallySurjective_of_isPullback (J := BigFppfOver.topology B S hS)
    (sq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))))

/-- **A base change of a quasi-compact formal algebraic space over an affine formal algebraic
space along a morphism from an affine formal algebraic space is quasi-compact.** Let `a : Z ⟶ Y'`
with `Z` a quasi-compact formal algebraic space and `Y'` an affine formal algebraic space, and let
`b : V ⟶ Y'` with `V` an affine formal algebraic space. Then any fibre product `Z ×_{Y'} V` is a
quasi-compact formal algebraic space.

The single affine formal chart `z : A ⟶ Z` of `Z` base changes to a representable étale
surjection onto the fibre product, whose source is `A ×_{Y'} V` by pasting the two cartesian
squares; that is an affine formal algebraic space by Stacks 0AN3 clause (1), the base `Y'` being
separated with representable relative products. -/
theorem isQuasiCompactSpace_of_isPullback_of_isAffineFormal
    {Z Y' V P : FppfSheaf B S hS} {a : Z ⟶ Y'} {b : V ⟶ Y'} {pz : P ⟶ Z} {pv : P ⟶ V}
    (sq : IsPullback pz pv a b) (hZ : IsQuasiCompactSpace B S hS Z)
    (hY' : IsAffineFormalAlgebraicSpace B S hS Y')
    (hV : IsAffineFormalAlgebraicSpace B S hS V) :
    IsQuasiCompactSpace B S hS P := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, A, z, hA, hz, hzsurj⟩ := hZ
  have hcomp : IsPullback (pullback.fst z pz) (pullback.snd z pz ≫ pv) (z ≫ a) b :=
    (IsPullback.of_hasPullback z pz).paste_vert sq
  have hQ : IsAffineFormalAlgebraicSpace B S hS (pullback z pz) :=
    isAffineFormalAlgebraicSpace_of_iso B S hS hcomp.isoPullback.symm
      (isAffineFormalAlgebraicSpace_pullback B S hS (z ≫ a) b
        (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hY')
        (IsAffineFormalAlgebraicSpace.isSeparated B S hS hY') hA hV)
  have hsnd : Sheaf.IsLocallySurjective (pullback.snd z pz) :=
    isLocallySurjective_of_isPullback_of_isLocallySurjective B S hS
      (IsPullback.of_hasPullback z pz).flip hzsurj
  refine isQuasiCompactSpace_of_finite_isRepresentableEtale_cover B S hS
    (I := PUnit.{u + 2}) (fun _ ↦ pullback z pz) (fun _ ↦ pullback.snd z pz)
    (fun _ ↦ isRepresentableEtale_pullback_snd B S hS z pz hz)
    (fun _ ↦ isQuasiCompactSpace_of_isAffineFormalAlgebraicSpace B S hS hQ) ?_
  have hcomp' : Epi (Sigma.ι (fun _ : PUnit.{u + 2} ↦ pullback z pz) PUnit.unit ≫
      Sigma.desc (fun _ : PUnit.{u + 2} ↦ pullback.snd z pz)) := by
    rw [Sigma.ι_comp_desc]
    exact (Sheaf.isLocallySurjective_iff_epi _).mp hsnd
  exact (Sheaf.isLocallySurjective_iff_epi _).mpr
    (epi_of_epi (Sigma.ι (fun _ : PUnit.{u + 2} ↦ pullback z pz) PUnit.unit) _)

/-- A fibre product of `f : X ⟶ Y` with a morphism `ρ ≫ c` factoring through a member
`c : Y' ⟶ Y` of a covering whose own fibre product with `f` is a quasi-compact formal algebraic
space is a quasi-compact formal algebraic space, as soon as `Y'` and the source of `ρ` are affine
formal algebraic spaces: the fibre product is `(Y' ×_Y X) ×_{Y'} V` by cancelling the cartesian
square of `c`, and
`AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_of_isPullback_of_isAffineFormal` applies. -/
theorem isQuasiCompactSpace_of_isPullback_comp
    {X Y Y' V P : FppfSheaf B S hS} {f : X ⟶ Y} {c : Y' ⟶ Y} {ρ : V ⟶ Y'}
    {a : P ⟶ V} {b : P ⟶ X} (sq : IsPullback a b (ρ ≫ c) f)
    (hqc : ∀ (W : FppfSheaf B S hS) (p : W ⟶ Y') (q : W ⟶ X),
      IsPullback p q c f → IsQuasiCompactSpace B S hS W)
    (hY' : IsAffineFormalAlgebraicSpace B S hS Y')
    (hV : IsAffineFormalAlgebraicSpace B S hS V) :
    IsQuasiCompactSpace B S hS P := by
  have hw : (a ≫ ρ) ≫ c = b ≫ f := (Category.assoc _ _ _).trans sq.w
  have s : IsPullback (pullback.lift (a ≫ ρ) b hw ≫ pullback.snd c f) a f (ρ ≫ c) := by
    rw [pullback.lift_snd]
    exact sq.flip
  have hleft : IsPullback (pullback.lift (a ≫ ρ) b hw) a (pullback.fst c f) ρ :=
    IsPullback.of_right s (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback c f).flip
  exact isQuasiCompactSpace_of_isPullback_of_isAffineFormal B S hS hleft
    (hqc _ _ _ (IsPullback.of_hasPullback c f)) hY' hV

/-! ### The implication (4) implies (3) -/

/-- **Stacks 0AJB, condition (4) implies condition (3).** Let `f : X ⟶ Y` be a morphism of fppf
sheaves on the big fppf site of `S` admitting a covering `{cⱼ : Yⱼ ⟶ Y}` as in Definition 0AIM
all of whose fibre products with `f` are quasi-compact formal algebraic spaces. Then every fibre
product of `f` with an affine scheme over `S` in the site mapping to `Y` is a quasi-compact formal
algebraic space; that is, `f` is quasi-compact in the sense of Stacks 0AJC.

Let `g : T ⟶ Y` with `T` affine. The base changes `Yⱼ ×_Y T` are objects `Vⱼ` of the site étale
over `T` (Stacks 0AIG); an affine open of some `Vⱼ` through each point of `T`, and
quasi-compactness of `T`, give finitely many affine objects `Uₖ` étale over `T`, covering it, each
mapping to a member `Yⱼ` compatibly with `g`. The fibre product `W = X ×_Y T` is covered along
representable étale morphisms by the finitely many `W ×_T Uₖ = X ×_Y Uₖ`, each of which is
quasi-compact by
`AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_of_isPullback_comp`, so `W` is quasi-compact
by `AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_of_finite_isRepresentableEtale_cover`. -/
@[stacks 0AJB "condition (4) implies condition (3)"]
theorem HasQuasiCompactFormalAtlas.isQuasiCompact {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : HasQuasiCompactFormalAtlas B S hS f) : IsQuasiCompact B S hS f := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  intro T hT g W p q sq
  obtain ⟨I, Yi, c, haff, het, hsurj, hqc⟩ := h
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) :=
    @Scheme.compactSpace_of_isAffine ((BigFppfOver.toScheme B S hS).obj T) hT
  obtain ⟨s, V, qv, ξ, hsqv, hqv, hcovv⟩ :=
    exists_finset_pullback_cover_of_compactSpace B S hS Yi c haff het hsurj g.hom
  -- an affine open of some `Vᵢ` through every point of `T`
  choose L U π hUaff hUopen hUsieve hUpts using
    fun i ↦ BigFppfOver.exists_affine_open_cover' B S hS (V i)
  choose i₀ hi₀ hx using hcovv
  choose y hy using hx
  choose l z hz using fun x ↦ hUpts (i₀ x) (y x)
  let r : ∀ x, U (i₀ x) (l x) ⟶ T := fun x ↦ π (i₀ x) (l x) ≫ qv (i₀ x)
  have hret : ∀ x, Etale ((BigFppfOver.toScheme B S hS).map (r x)) := by
    intro x
    have := hUopen (i₀ x) (l x)
    have := hqv (i₀ x)
    rw [Functor.map_comp]
    infer_instance
  have hrmem : ∀ x, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (r x)) := by
    intro x
    refine ⟨z x, ?_⟩
    simp only [r, Functor.map_comp, Scheme.Hom.comp_apply, hz, hy]
  have hropen : ∀ x, IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map (r x))) := fun x ↦
    have := hret x
    (Scheme.Hom.isOpenMap _).isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ Set.range ((BigFppfOver.toScheme B S hS).map (r x))) hropen
    (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hrmem x⟩)
  -- the finite affine étale covering of `T`
  let K : Type u := {x // x ∈ t}
  have : Finite K := inferInstance
  let Vk : K → BigFppfOver B S hS := fun k ↦ U (i₀ k.1) (l k.1)
  let vk : ∀ k, Vk k ⟶ T := fun k ↦ r k.1
  have hcov : Sieve.ofArrows Vk vk ∈ BigFppfOver.topology B S hS T := by
    change Sieve.ofArrows Vk vk ∈ BigFppfOver.baseOverTopology B S hS .fppf T
    refine BigFppfOver.ofArrows_mem_baseOverTopology B S hS Vk vk ?_
    refine (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, fun k ↦ ?_⟩
    · obtain ⟨x', hx', hxx'⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
      exact ⟨⟨x', hx'⟩, hxx'⟩
    · have := hret k.1
      exact ⟨inferInstance, inferInstance⟩
  set F : ULift.{u + 1} K → FppfSheaf B S hS := fun k => yonedaSheaf B S hS (Vk k.down)
    with hFdef
  set γ : ∀ k, F k ⟶ yonedaSheaf B S hS T :=
    fun k => ⟨(uliftYoneda.{u + 1}).map (vk k.down)⟩ with hγdef
  have hγet : ∀ k, IsRepresentableEtale B S hS (γ k) := fun k =>
    isRepresentableEtale_yonedaSheafMap B S hS (vk k.down) (hret k.down.1)
  have hγsurj : Sheaf.IsLocallySurjective (Sigma.desc γ) := by
    rw [Sheaf.isLocallySurjective_sigmaDesc_iff]
    intro W s
    refine ⟨Sieve.pullback s.down (Sieve.ofArrows Vk vk),
      (BigFppfOver.topology B S hS).pullback_stable _ hcov, ?_⟩
    rintro Z g ⟨Wi, b, c, ⟨i⟩, hfac⟩
    exact ⟨ULift.up i, ULift.up b, congrArg ULift.up hfac⟩
  have hδ : ∀ k, Sigma.ι F k ≫ Sigma.desc γ = γ k := fun k => Sigma.ι_comp_desc _ _
  -- each `γ k ≫ g` factors through a member of the covering of condition (4)
  let ρ : ∀ k, F k ⟶ Yi (i₀ k.down.1) := fun k =>
    ⟨(uliftYoneda.{u + 1}).map (π (i₀ k.down.1) (l k.down.1)) ≫ ξ (i₀ k.down.1)⟩
  have hρ : ∀ k, (Sigma.ι F k ≫ Sigma.desc γ) ≫ g = ρ k ≫ c (i₀ k.down.1) := by
    intro k
    rw [hδ]
    apply Sheaf.hom_ext
    change (uliftYoneda.{u + 1}).map (π (i₀ k.down.1) (l k.down.1) ≫ qv (i₀ k.down.1)) ≫ g.hom =
      ((uliftYoneda.{u + 1}).map (π (i₀ k.down.1) (l k.down.1)) ≫ ξ (i₀ k.down.1)) ≫
        (c (i₀ k.down.1)).hom
    simp only [Functor.map_comp, Category.assoc]
    exact congrArg ((uliftYoneda.{u + 1}).map (π (i₀ k.down.1) (l k.down.1)) ≫ ·)
      (hsqv (i₀ k.down.1)).w.symm
  obtain ⟨m, hm₁, -, ⟨hmcol⟩⟩ := Sheaf.exists_isColimit_cofan_pullback_of_comp
    (BigFppfOver.topology B S hS) (Sigma.ι F) (coproductIsCoproduct F) (Sigma.desc γ) p
  refine isQuasiCompactSpace_of_finite_isRepresentableEtale_cover B S hS
    (fun k => pullback p (Sigma.ι F k ≫ Sigma.desc γ))
    (fun k => pullback.fst p (Sigma.ι F k ≫ Sigma.desc γ)) (fun k => ?_) (fun k => ?_) ?_
  · exact isRepresentableEtale_of_isPullback B S hS
      (IsPullback.of_hasPullback p (Sigma.ι F k ≫ Sigma.desc γ)).flip
      (by rw [hδ k]; exact hγet k)
  · have sq' := (IsPullback.of_hasPullback p (Sigma.ι F k ≫ Sigma.desc γ)).flip.paste_vert sq
    rw [hρ k] at sq'
    exact isQuasiCompactSpace_of_isPullback_comp B S hS sq' (hqc (i₀ k.down.1))
      (haff (i₀ k.down.1))
      (isAffineFormalAlgebraicSpace_yonedaSheaf B S hS _ (hUaff (i₀ k.down.1) (l k.down.1)))
  · have : Epi (pullback.fst p (Sigma.desc γ)) := (Sheaf.isLocallySurjective_iff_epi _).mp
      (isLocallySurjective_of_isPullback_of_isLocallySurjective B S hS
        (IsPullback.of_hasPullback p (Sigma.desc γ)) hγsurj)
    set e := (coproductIsCoproduct
      (fun k => pullback p (Sigma.ι F k ≫ Sigma.desc γ))).coconePointUniqueUpToIso hmcol
      with hedef
    have he : e.hom ≫ pullback.fst p (Sigma.desc γ) =
        Sigma.desc fun k => pullback.fst p (Sigma.ι F k ≫ Sigma.desc γ) := by
      refine Sigma.hom_ext _ _ fun k => ?_
      have hcomp := IsColimit.comp_coconePointUniqueUpToIso_hom
        (coproductIsCoproduct fun k => pullback p (Sigma.ι F k ≫ Sigma.desc γ)) hmcol
        (Discrete.mk k)
      simp only [Cofan.mk_ι_app] at hcomp
      rw [← Category.assoc, hedef, hcomp, hm₁ k]
      exact (Sigma.ι_comp_desc (fun k => pullback.fst p (Sigma.ι F k ≫ Sigma.desc γ)) k).symm
    refine (Sheaf.isLocallySurjective_iff_epi _).mpr ?_
    rw [← he]
    infer_instance

/-! ### The four conditions -/

/-- **Stacks 0AJB.** Let `f : X ⟶ Y` be a morphism of formal algebraic spaces over `S`. The
following are equivalent:

1. the morphism `f_red : X_red ⟶ Y_red` induced between the reductions (Stacks 0AIN) is a
   quasi-compact morphism of algebraic spaces;
2. for every quasi-compact scheme `T` over `S` in the site and morphism `T ⟶ Y`, the fibre product
   `X ×_Y T` is a quasi-compact formal algebraic space;
3. the same for every affine scheme `T` over `S` in the site;
4. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM such that every `X ×_Y Yⱼ` is a
   quasi-compact formal algebraic space.

The reductions in condition (1) are the chosen ones,
`AlgebraicGeometry.FormalSpace.reduction`, and `f_red` is
`AlgebraicGeometry.FormalSpace.chosenReductionMap`. The cycle of implications is
(1) ⇒ (4) (`IsQuasiCompactOnReductions.hasQuasiCompactFormalAtlas`),
(4) ⇒ (3) (`HasQuasiCompactFormalAtlas.isQuasiCompact`),
(3) ⇒ (2) (`IsQuasiCompact.isQuasiCompactOnSchemeBaseChanges`)
and (2) ⇒ (1) (`IsQuasiCompactOnSchemeBaseChanges.isQuasiCompactULift_chosenReductionMap`). -/
@[stacks 0AJB "the equivalence of the four conditions"]
theorem tfae_isQuasiCompact {X Y : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE
      [Space.IsQuasiCompactULift.{u + 1} B S hS (chosenReductionMap B S hS hX hY f).hom,
        IsQuasiCompactOnSchemeBaseChanges B S hS f,
        IsQuasiCompact B S hS f,
        HasQuasiCompactFormalAtlas B S hS f] := by
  tfae_have 1 → 4 := fun h ↦ IsQuasiCompactOnReductions.hasQuasiCompactFormalAtlas B S hS
    ((isQuasiCompactOnReductions_iff_isQuasiCompactULift_chosenReductionMap B S hS hX hY f).mpr
      h) hX hY
  tfae_have 4 → 3 := HasQuasiCompactFormalAtlas.isQuasiCompact B S hS
  tfae_have 3 → 2 := IsQuasiCompact.isQuasiCompactOnSchemeBaseChanges B S hS
  tfae_have 2 → 1 :=
    IsQuasiCompactOnSchemeBaseChanges.isQuasiCompactULift_chosenReductionMap B S hS hX hY
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
