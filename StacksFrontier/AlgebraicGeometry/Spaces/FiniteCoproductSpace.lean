module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.VanKampen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.CategoryTheory.Limits.VanKampenCoproducts

/-!
# The clopen decomposition of a scheme by a section of a coproduct of sheaves

Let `F : I →` sheaves on the big fppf site of `S` be a family of algebraic spaces over `S`.
This file provides the decomposition machinery by which a morphism into a sheaf coproduct of
the `F i` is analysed summand by summand, and with it the two facts about a morphism out of a
coproduct of the site — surjectivity and étaleness — that are checked summand by summand.
`AlgebraicGeometry.isAlgebraicSpace_coproduct` is **Stacks 02WQ** itself and is proved
elsewhere, from the same geometric input and with no smallness hypothesis on the index type.

Everything rests on one geometric input, **Stacks 0F15**: each coproduct inclusion
`ι i : F i ⟶ G` is representable by morphisms which are simultaneously open and closed
immersions. Consequently a section `g : h_T ⟶ G` over a scheme `T` of the site cuts `T` into
clopen pieces `A i`, one for each summand, and because coproducts of sheaves of sets are
universal — the site is essentially small, so sheafification exists — those pieces exhibit
`h_T` as the *coproduct* of the `h_{A i}` (`exists_coproductDecomposition`). Pulling anything
back along `g` therefore decomposes it summand by summand
(`exists_isPullback_of_decomposition`), and the pieces are reassembled by the atlas
mechanism `AlgebraicGeometry.BigFppfOver.isColimit_yoneda_sigmaCofan`.

That decomposition is what makes the two conditions of Stacks 02WQ checkable: `h_T ×_G h_{T'}`
decomposes as the coproduct of the `h_{A i} ×_{F i} h_{B i}`, each representable by the
diagonal of `F i`, and `h_V ×_G h_T` decomposes as the coproduct of the
`h_{U i} ×_{F i} h_{A i}`, each surjective étale over `A i` by base change of the atlas of
`F i`.

## Main results

* `AlgebraicGeometry.coproductIncl_pullback_rep`: **Stacks 0F15**, in the form carrying the
  representing object of the site.
* `AlgebraicGeometry.exists_coproductDecomposition`: the clopen decomposition of a scheme of
  the site determined by a section of a coproduct of sheaves, together with the statement
  that it exhibits the representable sheaf of that scheme as a coproduct.
* `AlgebraicGeometry.exists_isPullback_coproduct`: the decomposition of a represented fibre
  product over a coproduct sheaf into the fibre products over the summands.

## Implementation notes

The index type is arbitrary and is allowed to live in any universe. What the source calls the
requirement that `I` and the `F i` be "not too large" appears here as two hypotheses: the
clopen pieces of a scheme of the site are reassembled into an object of the site, which asks
that the index type be admissible for coproducts in the site
(`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`) and `u`-small. Every finite index type
is both.

Universality of coproducts of sheaves of sets at an arbitrary index type is
`CategoryTheory.isUniversalColimit_of_isColimit_sheafOfTypes`; Mathlib's
`CategoryTheory.FinitaryExtensive` gives only the finite case, which is why the arbitrary
index needs the former.

Two small bridges between sheaves and presheaves are isolated at the top of the file:
`AlgebraicGeometry.isPullback_sheaf_of_hom` (a square of sheaves cartesian in presheaves is
cartesian in sheaves, since the inclusion of sheaves is fully faithful, hence reflects
limits) and `AlgebraicGeometry.isPullback_hom_of_sheaf` (the converse, which needs a left
adjoint and so is stated for a site admitting sheafification). They are needed because
`CategoryTheory.MorphismProperty.presheaf` — the form in which `Stacks 025Y` records
surjectivity and étaleness of an atlas — lives in presheaves, whereas the coproduct `G` and
all the colimit arguments live in sheaves.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 0F15](https://stacks.math.columbia.edu/tag/0F15)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

/-! ### Cartesian squares of sheaves of sets -/

section SheafSquares

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {W X Y Z : Sheaf J (Type u)} {fst : W ⟶ X} {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- A square of sheaves of sets which is cartesian in presheaves is cartesian in sheaves: the
inclusion of sheaves into presheaves is fully faithful, hence reflects limits. -/
theorem isPullback_sheaf_of_hom (h : IsPullback fst.hom snd.hom f.hom g.hom) :
    IsPullback fst snd f g :=
  IsPullback.of_map (sheafToPresheaf J (Type u)) (Sheaf.hom_ext h.w) h

/-- A cartesian square of sheaves of sets is cartesian in presheaves, provided the site admits
sheafification: the inclusion of sheaves into presheaves is then a right adjoint. -/
theorem isPullback_hom_of_sheaf [HasSheafify J (Type u)] (h : IsPullback fst snd f g) :
    IsPullback fst.hom snd.hom f.hom g.hom :=
  h.map (sheafToPresheaf J (Type u))

end SheafSquares

/-! ### Sheafification and extensivity for the big fppf site of `S` -/

section Instances

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Sheaves of sets on the big fppf site of `S` admit sheafification, the site being
essentially small.

This is `AlgebraicGeometry.BigFppfOver.hasSheafify_type` of
`StacksFrontier/AlgebraicGeometry/Topologies/BigFppfOverTypeSheafification.lean`, which is where
the proof lives: that module is devoted to this statement, its import closure is 250 against
this file's 362, and importing it costs one module. The name here is kept as an alias. -/
theorem bigFppfOver_hasSheafify :
    HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
  BigFppfOver.hasSheafify_type B S hS

end Instances

/-- A family of morphisms `R i ⟶ T` factors through the coproduct of the `R i` in the site. -/
private theorem exists_sigmaObj_hom (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} [Small.{u} I] [B.AdmitsCoproductIndex I] (R : I → BigFppfOver B S hS)
    {T : BigFppfOver B S hS} (f : ∀ i, R i ⟶ T) :
    ∃ σ : BigFppfOver.sigmaObj B S hS R ⟶ T, ∀ i, BigFppfOver.sigmaIncl B S hS R i ≫ σ = f i :=
  ⟨Cofan.IsColimit.desc (BigFppfOver.isColimit_sigmaCofan B S hS R) f,
    fun i => Cofan.IsColimit.fac (BigFppfOver.isColimit_sigmaCofan B S hS R) _ i⟩

/-! ### Stacks 0F15 with the representing object, for an arbitrary index type -/

section Decomposition

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [(BigFppfOver.topology B S hS).Subcanonical]
  {I : Type v} {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
  {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, Fi i ⟶ G)

omit [(BigFppfOver.topology B S hS).Subcanonical] in
/-- **Stacks 0F15**, for a coproduct over an arbitrary index type and in the form carrying the
representing object: for a coproduct `G` of sheaves `F i` on the big fppf site of `S` and a
section `γ : h_A ⟶ G`, the fibre product `h_A ×_G F i` is represented by an object `P` of the
site whose structure morphism `P ⟶ A` is both an open and a closed immersion of schemes. -/
theorem coproductIncl_pullback_rep (hc : IsColimit (Cofan.mk G ι)) (i : I)
    {A : BigFppfOver B S hS} (γ : yoneda.obj A ⟶ G.obj) :
    ∃ (P : BigFppfOver B S hS) (m : P ⟶ A) (f : yoneda.obj P ⟶ (Fi i).obj),
      IsPullback f (yoneda.map m) (ι i).hom γ ∧
        IsOpenImmersion ((BigFppfOver.toScheme B S hS).map m) ∧
        IsClosedImmersion ((BigFppfOver.toScheme B S hS).map m) :=
  coproductInl_pullback_rep B S hS (Fi i)
    (coproductComplement (fun j => (ι j).hom) i) G (ι i)
    (coproductComplementIncl (fun j => (ι j).hom) i)
    (isColimit_binaryCofan_coproductComplement ι hc i) γ

/-- **Stacks 0F15** for an arbitrary index type, read in the category of sheaves: the fibre
product of a section `γ : h_A ⟶ G` of a coproduct of sheaves with the `i`-th summand is
represented by a clopen piece of `A`. -/
theorem coproductIncl_sheafPullback_rep (hc : IsColimit (Cofan.mk G ι)) (i : I)
    (A : BigFppfOver B S hS)
    (γ : (BigFppfOver.topology B S hS).yoneda.obj A ⟶ G) :
    ∃ (P : BigFppfOver B S hS) (m : P ⟶ A)
      (f : (BigFppfOver.topology B S hS).yoneda.obj P ⟶ Fi i),
      IsPullback f ((BigFppfOver.topology B S hS).yoneda.map m) (ι i) γ ∧
        IsOpenImmersion ((BigFppfOver.toScheme B S hS).map m) ∧
        IsClosedImmersion ((BigFppfOver.toScheme B S hS).map m) := by
  obtain ⟨P, m, f, hpb, hopen, hclosed⟩ :=
    coproductIncl_pullback_rep B S hS ι hc i (A := A) γ.hom
  exact ⟨P, m, ⟨f⟩, isPullback_sheaf_of_hom hpb, hopen, hclosed⟩

/-- **The clopen decomposition of Stacks 02WQ.** A section `g : h_T ⟶ G` of a coproduct of a
family of sheaves on the big fppf site of `S` cuts `T` into clopen pieces `A i`, the `i`-th
being the fibre product `h_T ×_G F i`, and these exhibit the representable sheaf of `T` as
the coproduct of the representable sheaves of the `A i`.

The last assertion is the universality of coproducts in the category of sheaves of sets. -/
theorem exists_coproductDecomposition [Small.{u} I] [B.AdmitsCoproductIndex I]
    (hc : IsColimit (Cofan.mk G ι))
    (T : BigFppfOver B S hS)
    (g : (BigFppfOver.topology B S hS).yoneda.obj T ⟶ G) :
    ∃ (A : I → BigFppfOver B S hS) (α : ∀ i, A i ⟶ T)
      (s : ∀ i, (BigFppfOver.topology B S hS).yoneda.obj (A i) ⟶ Fi i),
      (∀ i, IsPullback (s i) ((BigFppfOver.topology B S hS).yoneda.map (α i)) (ι i) g) ∧
        Nonempty (IsColimit (Cofan.mk ((BigFppfOver.topology B S hS).yoneda.obj T)
          fun i => (BigFppfOver.topology B S hS).yoneda.map (α i))) ∧
        (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (α i))) ∧
        ∀ i, IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (α i)) := by
  classical
  have := AlgebraicGeometry.BigFppfOver.hasSheafify_type B S hS
  choose A α s hpb hopen hclosed using fun i =>
    coproductIncl_sheafPullback_rep B S hS ι hc i T g
  refine ⟨A, α, s, hpb, ?_, hopen, hclosed⟩
  refine isUniversalColimit_of_isColimit_sheafOfTypes _ hc
    (Cofan.mk ((BigFppfOver.topology B S hS).yoneda.obj T)
      fun i => (BigFppfOver.topology B S hS).yoneda.map (α i))
    (Discrete.natTrans fun k => s k.as) g ?_ (.of_discrete _) ?_
  · apply NatTrans.ext
    funext k
    obtain ⟨i⟩ := k
    simpa using (hpb i).w
  · rintro ⟨i⟩
    simpa using (hpb i).flip

/-- **The reassembly step of Stacks 02WQ.** Let `α i : A i ⟶ T` be a decomposition of a scheme
`T` of the site, in the sense that the representable sheaf of `T` is the coproduct of those of
the `A i`, and let `v : X ⟶ Z` be a morphism of sheaves over which each piece `A i` has a
representable fibre product `R i`. Then the coproduct of the `R i` in the site represents
`X ×_Z h_T`.

This is the universality of coproducts of sheaves of sets, combined with the atlas
mechanism `AlgebraicGeometry.BigFppfOver.isColimit_yoneda_sigmaCofan`, which turns the
coproduct of the `h_{R i}` back into a representable sheaf. -/
theorem exists_isPullback_of_decomposition [Small.{u} I] [B.AdmitsCoproductIndex I]
    {X Z : Sheaf (BigFppfOver.topology B S hS) (Type u)} (v : X ⟶ Z)
    {T : BigFppfOver B S hS}
    (u : (BigFppfOver.topology B S hS).yoneda.obj T ⟶ Z)
    (A : I → BigFppfOver B S hS) (α : ∀ i, A i ⟶ T)
    (hT : IsColimit (Cofan.mk ((BigFppfOver.topology B S hS).yoneda.obj T)
      fun i => (BigFppfOver.topology B S hS).yoneda.map (α i)))
    (R : I → BigFppfOver B S hS)
    (r : ∀ i, (BigFppfOver.topology B S hS).yoneda.obj (R i) ⟶ X) (ρ : ∀ i, R i ⟶ A i)
    (hR : ∀ i, IsPullback (r i) ((BigFppfOver.topology B S hS).yoneda.map (ρ i)) v
      ((BigFppfOver.topology B S hS).yoneda.map (α i) ≫ u)) :
    ∃ (σ : BigFppfOver.sigmaObj B S hS R ⟶ T)
      (fst : (BigFppfOver.topology B S hS).yoneda.obj (BigFppfOver.sigmaObj B S hS R) ⟶ X),
      (∀ i, BigFppfOver.sigmaIncl B S hS R i ≫ σ = ρ i ≫ α i) ∧
        IsPullback fst ((BigFppfOver.topology B S hS).yoneda.map σ) v u := by
  have := AlgebraicGeometry.BigFppfOver.hasSheafify_type B S hS
  have key := (isUniversalColimit_of_isColimit_sheafOfTypes _ hT).isPullback_of_isColimit_left
    (fun i => (BigFppfOver.topology B S hS).yoneda.map (α i) ≫ u) u v r
    (fun i => (BigFppfOver.topology B S hS).yoneda.map (ρ i)) hR
    (BigFppfOver.isColimit_yoneda_sigmaCofan B S hS R) (fun i => rfl)
  obtain ⟨σ, hσ⟩ := exists_sigmaObj_hom B S hS R fun i => ρ i ≫ α i
  refine ⟨σ, Cofan.IsColimit.desc (BigFppfOver.isColimit_yoneda_sigmaCofan B S hS R) r, hσ, ?_⟩
  have hsnd : (Cofan.IsColimit.desc (BigFppfOver.isColimit_yoneda_sigmaCofan B S hS R)
        fun i => (BigFppfOver.topology B S hS).yoneda.map (ρ i) ≫
          (Cofan.mk ((BigFppfOver.topology B S hS).yoneda.obj T)
            fun k => (BigFppfOver.topology B S hS).yoneda.map (α k)).inj i) =
      (BigFppfOver.topology B S hS).yoneda.map σ := by
    refine Cofan.IsColimit.hom_ext
      (BigFppfOver.isColimit_yoneda_sigmaCofan B S hS R) _ _ fun i => ?_
    rw [Cofan.IsColimit.fac]
    simp only [Cofan.inj, Cofan.mk_ι_app]
    rw [← Functor.map_comp, ← Functor.map_comp, hσ]
  exact hsnd ▸ key

end Decomposition

/-! ### Surjectivity and étaleness out of a coproduct of the site -/

section Properties

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {I : Type v}
  [Small.{u} I] [B.AdmitsCoproductIndex I]

/-- The summands of a coproduct of the big fppf site of `S` form an open cover of its
underlying scheme. -/
noncomputable def BigFppfOver.sigmaObjOpenCover (U : I → BigFppfOver B S hS) :
    ((BigFppfOver.toScheme B S hS).obj (BigFppfOver.sigmaObj B S hS U)).OpenCover :=
  (sigmaOpenCover fun i => (BigFppfOver.toScheme B S hS).obj (U i)).copy I
    (fun i => (BigFppfOver.toScheme B S hS).obj (U i))
    (fun i => (BigFppfOver.toScheme B S hS).map (BigFppfOver.sigmaIncl B S hS U i))
    (Equiv.refl I) (fun _ => Iso.refl _)
    (fun i => (BigFppfOver.toScheme_map_sigmaIncl B S hS U i).trans (Category.id_comp _).symm)

/-- The `i`-th morphism of `BigFppfOver.sigmaObjOpenCover` is the image under
`BigFppfOver.toScheme` of the `i`-th coproduct inclusion. -/
@[simp]
theorem BigFppfOver.sigmaObjOpenCover_f (U : I → BigFppfOver B S hS) (i : I) :
    (BigFppfOver.sigmaObjOpenCover B S hS U).f i =
      (BigFppfOver.toScheme B S hS).map (BigFppfOver.sigmaIncl B S hS U i) := rfl

/-- Every point of the underlying scheme of a coproduct of the big fppf site of `S` lies
in one of the summands. -/
theorem BigFppfOver.exists_apply_eq_sigmaIncl (U : I → BigFppfOver B S hS)
    (z : ((BigFppfOver.toScheme B S hS).obj (BigFppfOver.sigmaObj B S hS U) : Type u)) :
    ∃ (i : I) (y : ((BigFppfOver.toScheme B S hS).obj (U i) : Type u)),
      (BigFppfOver.toScheme B S hS).map (BigFppfOver.sigmaIncl B S hS U i) y = z := by
  obtain ⟨i, y, hy⟩ := (BigFppfOver.sigmaObjOpenCover B S hS U).exists_eq z
  exact ⟨i, y, hy⟩

/-- Étaleness of a morphism out of a coproduct of the big fppf site of `S` is checked
summand by summand: étaleness is local on the source, and the summands cover. -/
theorem etale_toScheme_of_sigmaIncl {T : BigFppfOver B S hS} (R : I → BigFppfOver B S hS)
    (σ : BigFppfOver.sigmaObj B S hS R ⟶ T)
    (h : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map
      (BigFppfOver.sigmaIncl B S hS R i ≫ σ))) :
    Etale ((BigFppfOver.toScheme B S hS).map σ) := by
  have : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
  refine IsZariskiLocalAtSource.of_openCover (BigFppfOver.sigmaObjOpenCover B S hS R) ?_
  intro i
  have key : (BigFppfOver.sigmaObjOpenCover B S hS R).f i ≫
        (BigFppfOver.toScheme B S hS).map σ =
      (BigFppfOver.toScheme B S hS).map
        (BigFppfOver.sigmaIncl B S hS R (show I from i) ≫ σ) :=
    ((BigFppfOver.toScheme B S hS).map_comp
      (BigFppfOver.sigmaIncl B S hS R (show I from i)) σ).symm
  rw [key]
  exact h _

/-- A decomposition of a scheme `T` of the site — a family `α i : A i ⟶ T` exhibiting
the representable sheaf of `T` as the coproduct of those of the `A i` — identifies the
coproduct of the `A i` *in the site* with `T`, the Yoneda embedding into sheaves being fully
faithful for a subcanonical topology. -/
theorem isIso_of_decomposition [(BigFppfOver.topology B S hS).Subcanonical]
    {T : BigFppfOver B S hS} (A : I → BigFppfOver B S hS) (α : ∀ i, A i ⟶ T)
    (hT : IsColimit (Cofan.mk ((BigFppfOver.topology B S hS).yoneda.obj T)
      fun i => (BigFppfOver.topology B S hS).yoneda.map (α i)))
    (σ : BigFppfOver.sigmaObj B S hS A ⟶ T)
    (hσ : ∀ i, BigFppfOver.sigmaIncl B S hS A i ≫ σ = α i) : IsIso σ := by
  have hmap : (BigFppfOver.topology B S hS).yoneda.map σ =
      ((BigFppfOver.isColimit_yoneda_sigmaCofan B S hS A).coconePointUniqueUpToIso hT).hom := by
    refine Cofan.IsColimit.hom_ext
      (BigFppfOver.isColimit_yoneda_sigmaCofan B S hS A) _ _ fun i => ?_
    simp only [Cofan.inj]
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    simp only [Cofan.mk_ι_app]
    rw [← Functor.map_comp, hσ]
  have : IsIso ((BigFppfOver.topology B S hS).yoneda.map σ) := by
    rw [hmap]
    infer_instance
  exact Functor.FullyFaithful.isIso_of_isIso_map
    (BigFppfOver.topology B S hS).yonedaFullyFaithful σ

/-- Surjectivity of a morphism out of a coproduct of the big fppf site of `S`, when the
target is the coproduct of a family of its clopen pieces: every point of the target lies in one
piece, and each piece is hit. -/
theorem surjective_toScheme_of_sigmaIncl {T : BigFppfOver B S hS} (A : I → BigFppfOver B S hS)
    (α : ∀ i, A i ⟶ T) (σA : BigFppfOver.sigmaObj B S hS A ⟶ T) [IsIso σA]
    (hσA : ∀ i, BigFppfOver.sigmaIncl B S hS A i ≫ σA = α i)
    (R : I → BigFppfOver B S hS) (ρ : ∀ i, R i ⟶ A i)
    (σ : BigFppfOver.sigmaObj B S hS R ⟶ T)
    (hσ : ∀ i, BigFppfOver.sigmaIncl B S hS R i ≫ σ = ρ i ≫ α i)
    (hρ : ∀ i, Surjective ((BigFppfOver.toScheme B S hS).map (ρ i))) :
    Surjective ((BigFppfOver.toScheme B S hS).map σ) := by
  rw [surjective_iff]
  intro t
  obtain ⟨z, hz⟩ := (surjective_iff ((BigFppfOver.toScheme B S hS).map σA)).mp inferInstance t
  obtain ⟨i, y, hy⟩ := BigFppfOver.exists_apply_eq_sigmaIncl B S hS A z
  obtain ⟨x, hx⟩ := (surjective_iff _).mp (hρ i) y
  refine ⟨(BigFppfOver.toScheme B S hS).map (BigFppfOver.sigmaIncl B S hS R i) x, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hσ, Functor.map_comp, Scheme.Hom.comp_apply,
    hx, ← hσA, Functor.map_comp, Scheme.Hom.comp_apply, hy, hz]

end Properties

/-! ### Stacks 02WQ -/

section Main

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [(BigFppfOver.topology B S hS).Subcanonical]
  {I : Type v} [Small.{u} I] [B.AdmitsCoproductIndex I]
  {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
  {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, Fi i ⟶ G)

/-- **The atlas of a coproduct, summand by summand.** Let `V` be a coproduct in the big
fppf site of `S` of a family `U`, let `G` be a sheaf coproduct of sheaves `F i`, and let
`q : h_V ⟶ G` be assembled from morphisms `fU i : h_{U i} ⟶ F i`. Then `h_{U i}` is the fibre
product of `q` with the `i`-th coproduct inclusion.

This is the van Kampen property of coproducts in the category of sheaves of sets. -/
theorem isPullback_coproductIncl_atlas (hc : IsColimit (Cofan.mk G ι))
    (U : I → BigFppfOver B S hS) {V : BigFppfOver B S hS} (j : ∀ i, U i ⟶ V)
    (hV : IsColimit (Cofan.mk V j))
    (fU : ∀ i, (BigFppfOver.topology B S hS).yoneda.obj (U i) ⟶ Fi i)
    (q : (BigFppfOver.topology B S hS).yoneda.obj V ⟶ G)
    (hq : ∀ i, (BigFppfOver.topology B S hS).yoneda.map (j i) ≫ q = fU i ≫ ι i) (i : I) :
    IsPullback ((BigFppfOver.topology B S hS).yoneda.map (j i)) (fU i) q (ι i) := by
  have := AlgebraicGeometry.BigFppfOver.hasSheafify_type B S hS
  have hcomp : (Discrete.natTrans fun k => fU k.as) ≫ (Cofan.mk G ι).ι =
      (Cofan.mk ((BigFppfOver.topology B S hS).yoneda.obj V)
        fun k => (BigFppfOver.topology B S hS).yoneda.map (j k)).ι ≫
        (Functor.const (Discrete I)).map q := by
    apply NatTrans.ext
    funext k
    obtain ⟨m⟩ := k
    simpa using (hq m).symm
  have H := isVanKampenColimit_of_isColimit_sheafOfTypes _ hc
    (Cofan.mk ((BigFppfOver.topology B S hS).yoneda.obj V)
      fun k => (BigFppfOver.topology B S hS).yoneda.map (j k))
    (Discrete.natTrans fun k => fU k.as) q hcomp (.of_discrete _)
  simpa using H.mp ⟨BigFppfOver.isColimit_yoneda_cofan B S hS U j hV⟩ (Discrete.mk i)

/-- **The core of Stacks 02WQ.** Let `G` be a sheaf coproduct of a family `F i` on the
big fppf site of `S`, let `v : X ⟶ G` be a morphism of sheaves whose fibre product with the
`i`-th summand is the representable sheaf of an object `C i` of the site, and let `u : h_T ⟶ G`
be a section over a scheme `T` of the site.

Then `X ×_G h_T` is represented by a coproduct `∐ R i` of the site: the section `u`
decomposes `T` into clopen pieces `A i`, over which `v` becomes the morphism `h_{C i} ⟶ F i`,
and `R i` represents `h_{C i} ×_{F i} h_{A i}`. The data returned is everything the two
conditions of `Stacks 025Y` need: the cartesian square, the factorizations of the two
coproduct morphisms, and the identification of `T` with the coproduct of the `A i`. -/
theorem exists_isPullback_coproduct (hc : IsColimit (Cofan.mk G ι))
    {X : Sheaf (BigFppfOver.topology B S hS) (Type u)} (v : X ⟶ G)
    (C : I → BigFppfOver B S hS)
    (χ : ∀ i, (BigFppfOver.topology B S hS).yoneda.obj (C i) ⟶ X)
    (c : ∀ i, (BigFppfOver.topology B S hS).yoneda.obj (C i) ⟶ Fi i)
    (hC : ∀ i, IsPullback (χ i) (c i) v (ι i))
    (hrep : ∀ i, yoneda.relativelyRepresentable (c i).hom)
    (T : BigFppfOver B S hS) (u : (BigFppfOver.topology B S hS).yoneda.obj T ⟶ G) :
    ∃ (A R : I → BigFppfOver B S hS) (α : ∀ i, A i ⟶ T) (ρ : ∀ i, R i ⟶ A i)
      (ζ : ∀ i, R i ⟶ C i)
      (s : ∀ i, (BigFppfOver.topology B S hS).yoneda.obj (A i) ⟶ Fi i)
      (σ : BigFppfOver.sigmaObj B S hS R ⟶ T)
      (σA : BigFppfOver.sigmaObj B S hS A ⟶ T)
      (fst : (BigFppfOver.topology B S hS).yoneda.obj (BigFppfOver.sigmaObj B S hS R) ⟶ X),
      IsIso σA ∧
        (∀ i, BigFppfOver.sigmaIncl B S hS A i ≫ σA = α i) ∧
        (∀ i, BigFppfOver.sigmaIncl B S hS R i ≫ σ = ρ i ≫ α i) ∧
        IsPullback fst ((BigFppfOver.topology B S hS).yoneda.map σ) v u ∧
        (∀ i, IsPullback (yoneda.map (ζ i)) (yoneda.map (ρ i)) (c i).hom (s i).hom) ∧
        ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (α i)) := by
  classical
  obtain ⟨A, α, s, hsq, ⟨hT⟩, hopen, -⟩ := exists_coproductDecomposition B S hS ι hc T u
  choose R ρ fst0 hinner using fun i => hrep i ((s i).hom)
  have hY : ∀ i, IsPullback (yoneda.map (yoneda.preimage (fst0 i))) (yoneda.map (ρ i))
      (c i).hom (s i).hom := by
    intro i
    rw [Functor.map_preimage]
    exact hinner i
  have hRsq : ∀ i, IsPullback
      ((BigFppfOver.topology B S hS).yoneda.map (yoneda.preimage (fst0 i)) ≫ χ i)
      ((BigFppfOver.topology B S hS).yoneda.map (ρ i)) v
      ((BigFppfOver.topology B S hS).yoneda.map (α i) ≫ u) := by
    intro i
    have h := (isPullback_sheaf_of_hom
      (fst := (BigFppfOver.topology B S hS).yoneda.map (yoneda.preimage (fst0 i)))
      (snd := (BigFppfOver.topology B S hS).yoneda.map (ρ i)) (f := c i) (g := s i)
      (hY i)).paste_horiz (hC i)
    rwa [(hsq i).w] at h
  obtain ⟨σ, fstσ, hfacσ, hpbσ⟩ :=
    exists_isPullback_of_decomposition B S hS v u A α hT R
      (fun i => (BigFppfOver.topology B S hS).yoneda.map (yoneda.preimage (fst0 i)) ≫ χ i)
      ρ hRsq
  obtain ⟨σA, hfacA⟩ := exists_sigmaObj_hom B S hS A α
  exact ⟨A, R, α, ρ, fun i => yoneda.preimage (fst0 i), s, σ, σA, fstσ,
    isIso_of_decomposition B S hS A α hT σA hfacA, hfacA, hfacσ, hpbσ, hY, hopen⟩

end Main

end AlgebraicGeometry

end
