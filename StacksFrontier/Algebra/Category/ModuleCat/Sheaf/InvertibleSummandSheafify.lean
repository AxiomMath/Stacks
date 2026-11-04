module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleLocalSummand
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorInvertible
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksCore.Tactic.StacksAttribute

/-!
# Invertible modules are locally direct summands of finite free modules

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `L` be an invertible sheaf of
`O`-modules, i.e. one for which tensoring is an equivalence of the category of sheaves of
`O`-modules. Stacks Tag 0B8N (b) asserts that every object `U` of `C` admits a covering
`{V i → U}` on whose members `L` restricts to a direct summand of a finite free module. This file
proves that statement.

The ingredients that are purely algebraic — the fact that a universal map into a sheaf of modules
is locally surjective, and the splitting produced by a dual basis for the tensor pairing — are in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleLocalSummand.lean`. What this file adds is
the local *injectivity* of the universal map, the comparison of a tensor product of presheaves of
modules with the tensor product of its restrictions to a slice site, and the assembly.

## Main definitions

* `Stacks.SheafOfModules.slicePairing`: the restriction of a pairing
  `Lp ⊗ Np ⟶ O` to a slice site, formed with the monoidal comparison maps of `sliceFunctor`.
* `Stacks.SheafOfModules.sliceSection`: a section over `V` of a presheaf of modules, viewed as a
  global section of its restriction to the slice site over `V`.

## Main results

* `Stacks.SheafOfModules.isLocallyInjective_of_universal`: a morphism of presheaves of modules
  `ψ : K ⟶ A.val` into a sheaf of modules through which every morphism to a sheaf of modules
  factors uniquely is locally injective.
* `Stacks.SheafOfModules.exists_locallyBijective_pairing`: an invertible sheaf of modules admits a
  locally bijective pairing `L.val ⊗ Np ⟶ O` of presheaves of modules.
* `Stacks.SheafOfModules.exists_isSplitMono_over`: the single-object form of Tag 0B8N (b), from a
  dual basis of sections over that object.
* `Stacks.SheafOfModules.exists_fin_tmul_eq`: every element of a tensor product of modules is a
  sum of finitely many pure tensors, indexed by `Fin n`.

## Implementation notes

Invertibility is `Stacks.SheafOfModules.IsInvertible` (Tag 01CS): tensoring by `L` is an
equivalence, where the tensor functor is pinned down by the universal property of the associated
sheaf of the pointwise presheaf tensor product. From it one extracts a module `Np` and a pairing
`ψ : L.val ⊗ Np ⟶ O` of *presheaves* of modules which is universal among maps into sheaves of
modules. Local surjectivity of `ψ` holds on any site whatsoever
(`isLocallySurjective_of_universal`); local injectivity does not, and this is the one place
sheafification is used: `isLocallyInjective_of_universal` compares `ψ` with the sheafification
unit `K ⟶ K^#`, which exists by `HasWeakSheafify J AddCommGrpCat` and is locally injective by
`J.WEqualsLocallyBijective AddCommGrpCat`. Local injectivity of `ψ` is exactly what is needed to
factor the projection `L ⊗ N ⟶ L` of Stacks' proof through `ψ`, i.e. to read that projection on
the *sheaf* tensor product rather than on the presheaf one. These hypotheses are assumed by the
Stacks statement itself, whose part (2) names the sheaf tensor product `L ⊗_O N ≅ O`. Nothing
here uses that `SheafOfModules O` is abelian, so `HasWeakSheafify` suffices in place of
`HasSheafify` and no `HasSheafCompose` instance is required.

Because the conclusion is a statement about the slice sites `C/V i`, the same universal property
is needed there, which is why `(J.over V).WEqualsLocallyBijective AddCommGrpCat` is assumed for
every `V`. No slice-site sheafification functor is needed, only the identification of the class
it inverts.

The comparison between the restriction of `Lp ⊗ Np` to a slice site and the tensor product of
the restrictions is not proved by hand: restriction is spelled as
`PresheafOfModules.pushforward₀OfCommRingCat`, which Mathlib equips with a `Functor.Monoidal`
instance, and `slicePairing` is built from its `μIso` and `εIso`. Both of these are componentwise
the identity (`slicePairing_app` is `rfl`), while asking for the functor-level equality of the two
tensor products directly exceeds the heartbeat limit. The underlying presheaf of
`(L.over V).val` is definitionally `(sliceFunctor V).obj L.val`, so the conclusion is stated with
Mathlib's `SheafOfModules.over` and `Sheaf.over` with no transport.

Local bijectivity transfers to a slice site because `Over.forget V` is cocontinuous for
`J.over V` and `J` (`Presheaf.isLocallySurjective_whisker` and its injective counterpart); on
underlying presheaves the pushforward of a morphism is literally the whiskering by
`(Over.forget V).op`.

The covering family is produced from the image sieve of `ψ` at the unit section `1`: its index
type is `Σ V : C, {g : V ⟶ U // S.arrows g}`, which lives in `Type (max u v)`, and the sieve it
generates contains `S`, hence is covering. On each member, the local preimage of `1` is an element
of a presheaf tensor product, hence a finite sum `∑ x j ⊗ₜ y j` of pure tensors with
`ψ (∑ x j ⊗ₜ y j) = 1`, which is the dual basis fed to `isSplitMono_of_dualBasis`.

Universes are those of the Stacks Tag 05NA formalization: the site objects and morphisms live
in independent universes `u` and `v`, while the ring and module sections share a universe `w`, as
Mathlib's monoidal structure on presheaves of modules requires. Nothing relates `w` to the size of
the site.

## References

* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Universal

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {R : Sheaf J RingCat.{w}}

/-- A universal map into a sheaf of modules is locally injective. -/
theorem isLocallyInjective_of_universal {K : PresheafOfModules.{w} R.obj}
    {A : SheafOfModules.{w} R} (ψ : K ⟶ A.val)
    (h : ∀ S : SheafOfModules.{w} R, Function.Bijective fun g : A ⟶ S => ψ ≫ g.val) :
    PresheafOfModules.IsLocallyInjective J ψ := by
  set η : K ⟶ ((PresheafOfModules.sheafification (𝟙 R.obj)).obj K).val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app K with hη
  obtain ⟨k, hk⟩ := (h ((PresheafOfModules.sheafification (𝟙 R.obj)).obj K)).surjective η
  have hinst : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R.obj).map η) :=
    inferInstanceAs
      (Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J K.presheaf))
  refine Presheaf.isLocallyInjective_of_isLocallyInjective_fac J
    (ψ := (PresheafOfModules.toPresheaf R.obj).map k.val)
    (φψ := (PresheafOfModules.toPresheaf R.obj).map η) ?_
  rw [← Functor.map_comp]
  exact (PresheafOfModules.toPresheaf R.obj).congr_map hk

end Universal

section Pairing

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)}

/-- An invertible sheaf of modules admits a locally bijective pairing with some presheaf of
modules. -/
theorem exists_locallyBijective_pairing
    {Lp : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)}
    (hLp : Presheaf.IsSheaf J Lp.presheaf)
    (hL : IsInvertible O hO (⟨Lp, hLp⟩ : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))) :
    ∃ (Np : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O))
      (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))),
      PresheafOfModules.IsLocallySurjective J ψ ∧
        PresheafOfModules.IsLocallyInjective J ψ := by
  obtain ⟨F, hF, ⟨a⟩⟩ := hL.exists_tensorFunctor
  have := hF
  set N := F.objPreimage (SheafOfModules.unit
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) with hN
  set e := F.objObjPreimageIso (SheafOfModules.unit
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) with he
  have huniv : ∀ S : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
    hO),
      Function.Bijective fun g : SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⟶ S =>
        (a.ι.app N ≫ e.hom.val) ≫ g.val := by
    intro S
    have hb : Function.Bijective
        (fun g : SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO) ⟶ S => e.hom ≫ g) := by
      refine ⟨fun g₁ g₂ hg => ?_, fun f => ⟨e.inv ≫ f, ?_⟩⟩
      · simpa using congrArg (fun t => e.inv ≫ t) hg
      · simp
    have hfun : (fun g : SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⟶ S =>
          (a.ι.app N ≫ e.hom.val) ≫ g.val)
        = (fun f : F.obj N ⟶ S =>
            a.ι.app N ≫ (SheafOfModules.forget
              (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).map f) ∘
          (fun g => e.hom ≫ g) := by
      funext g
      exact Category.assoc _ _ _
    rw [hfun]
    exact (a.bijective N S).comp hb
  exact ⟨N.val, a.ι.app N ≫ e.hom.val,
    isLocallySurjective_of_universal (A := SheafOfModules.unit _) _ huniv,
    isLocallyInjective_of_universal (A := SheafOfModules.unit _) _ huniv⟩

end Pairing

section Slice

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}}

lemma isLocallySurjective_sliceFunctor_map (V : C)
    {Lp Np : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)} (ψ : Lp ⟶ Np)
    [PresheafOfModules.IsLocallySurjective J ψ] :
    PresheafOfModules.IsLocallySurjective (J.over V) ((sliceFunctor (O := O) V).map ψ) :=
  Presheaf.isLocallySurjective_whisker (J.over V) J (Over.forget V)
    ((PresheafOfModules.toPresheaf _).map ψ)

lemma isLocallyInjective_sliceFunctor_map (V : C)
    {Lp Np : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)} (ψ : Lp ⟶ Np)
    [PresheafOfModules.IsLocallyInjective J ψ] :
    PresheafOfModules.IsLocallyInjective (J.over V) ((sliceFunctor (O := O) V).map ψ) :=
  Presheaf.isLocallyInjective_whisker (J.over V) J (Over.forget V)
    ((PresheafOfModules.toPresheaf _).map ψ)

/-- The restriction of a pairing `Lp ⊗ Np ⟶ O` to a slice site. -/
noncomputable def slicePairing (V : C)
    {Lp Np : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)}
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))) :
    (sliceFunctor (O := O) V).obj Lp ⊗ (sliceFunctor (O := O) V).obj Np ⟶
      𝟙_ (PresheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf ((Over.forget V).op ⋙ O)))
          :=
  (Functor.Monoidal.μIso (sliceFunctor (O := O) V) Lp Np).hom ≫
    (sliceFunctor (O := O) V).map ψ ≫ (Functor.Monoidal.εIso (sliceFunctor (O := O) V)).inv

lemma slicePairing_app (V : C)
    {Lp Np : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)}
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    (W : (Over V)ᵒᵖ) (z : ((sliceFunctor (O := O) V).obj Lp ⊗
      (sliceFunctor (O := O) V).obj Np).obj W) :
    (slicePairing V ψ).app W z = ψ.app (op W.unop.left) z := rfl

instance isLocallySurjective_slicePairing (V : C)
    {Lp Np : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)}
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    [PresheafOfModules.IsLocallySurjective J ψ] :
    PresheafOfModules.IsLocallySurjective (J.over V) (slicePairing V ψ) := by
  have h := isLocallySurjective_sliceFunctor_map (J := J) (O := O) V ψ
  dsimp only [slicePairing, PresheafOfModules.IsLocallySurjective]
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

instance isLocallyInjective_slicePairing (V : C)
    {Lp Np : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)}
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    [PresheafOfModules.IsLocallyInjective J ψ] :
    PresheafOfModules.IsLocallyInjective (J.over V) (slicePairing V ψ) := by
  have h := isLocallyInjective_sliceFunctor_map (J := J) (O := O) V ψ
  dsimp only [slicePairing, PresheafOfModules.IsLocallyInjective]
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- A section over `V` of a presheaf of modules is a global section of its restriction to the
slice site over `V`. -/
noncomputable def sliceSection (V : C)
    {Lp : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)} (a : Lp.obj (op V)) :
    ((sliceFunctor (O := O) V).obj Lp).sections :=
  PresheafOfModules.sectionsMk (fun W => Lp.map (W.unop.hom).op a) (fun {W W'} f => by
    change Lp.map (f.unop.left).op (Lp.map (W.unop.hom).op a) = Lp.map (W'.unop.hom).op a
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w f.unop])

@[simp]
lemma sliceSection_eval (V : C)
    {Lp : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)} (a : Lp.obj (op V))
    (W : (Over V)ᵒᵖ) :
    (sliceSection V a).eval W = Lp.map (W.unop.hom).op a := rfl

/-- **Stacks Project, Tag 0B8N (b), slice step.** A dual basis for a locally bijective pairing
over a single object `V` exhibits the restriction of `L` to the slice site over `V` as a direct
summand of a finite free module. -/
theorem exists_isSplitMono_over (V : C)
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    {Lp Np : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)}
    (hLp : Presheaf.IsSheaf J Lp.presheaf)
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    [PresheafOfModules.IsLocallySurjective J ψ] [PresheafOfModules.IsLocallyInjective J ψ]
    {n : ℕ} (x : Fin n → Lp.obj (op V)) (y : Fin n → Np.obj (op V))
    (hxy : ∑ j, ψ.app (op V) (x j ⊗ₜ y j) = (1 : O.obj (op V))) :
    ∃ s : (⟨Lp, hLp⟩ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      O hO)).over V ⟶
        ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
          ((Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).over V),
      IsSplitMono s := by
  classical
  refine isSplitMono_of_dualBasis (J := J.over V)
    (Lp := (sliceFunctor (O := O) V).obj Lp) (Np := (sliceFunctor (O := O) V).obj Np)
    (hO := (Over.forget V).op_comp_isSheaf_of_isSheaf (J.over V) J _ hO)
    (hLp := (Over.forget V).op_comp_isSheaf_of_isSheaf (J.over V) J _ hLp)
    (slicePairing V ψ) (fun j => sliceSection V (x j)) (fun j => sliceSection V (y j))
    (fun W j => (𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))).map
      (W.unop.hom).op (ψ.app (op V) (x j ⊗ₜ y j)))
    (fun W j => ?_) (fun W => ?_)
  · exact PresheafOfModules.naturality_apply ψ (W.unop.hom).op (x j ⊗ₜ y j)
  · have hs : ∑ j, (𝟙_ (PresheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))).map
          (W.unop.hom).op (ψ.app (op V) (x j ⊗ₜ y j))
        = (𝟙_ (PresheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))).map
          (W.unop.hom).op (∑ j, ψ.app (op V) (x j ⊗ₜ y j)) :=
      (map_sum _ _ _).symm
    refine hs.trans ((congrArg (fun z =>
      (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        O))).map
        (W.unop.hom).op z) hxy).trans ?_)
    exact PresheafOfModules.unit_map_one _ _

end Slice

section Main

/-- Every element of a tensor product is a sum of `n` pure tensors for some `n : ℕ`. -/
lemma exists_fin_tmul_eq {Rg : Type*} [CommRing Rg] {M N : Type*} [AddCommGroup M] [Module Rg M]
    [AddCommGroup N] [Module Rg N] (t : M ⊗[Rg] N) :
    ∃ (n : ℕ) (x : Fin n → M) (y : Fin n → N), ∑ j, x j ⊗ₜ[Rg] y j = t := by
  classical
  have ht : t ∈ Submodule.span Rg {z : M ⊗[Rg] N | ∃ a b, a ⊗ₜ[Rg] b = z} := by
    rw [TensorProduct.span_tmul_eq_top]; exact Submodule.mem_top
  obtain ⟨n, cf, g, hg⟩ := Submodule.mem_span_set'.mp ht
  choose a b hab using fun j => (g j).2
  refine ⟨n, fun j => cf j • a j, b, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hab j]
  rfl

end Main

end Stacks.SheafOfModules

end
