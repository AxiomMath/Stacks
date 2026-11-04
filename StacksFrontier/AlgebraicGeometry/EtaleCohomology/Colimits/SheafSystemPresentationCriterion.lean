module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystemSectionsColimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.HigherDirectImageLocalVanishing
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Recognising the colimit of a system of étale sheaves on a limit of schemes

Let `X = lim X_i` be the limit of a directed inverse system of schemes with affine transition
morphisms, let `(F_i, φ_{i'i})` be a system of abelian sheaves on the small étale sites of the
`X_i` ([Stacks, Tag 0EZL]) and let `ψ_i : f_i⁻¹F_i ⟶ 𝓑` be a compatible family of maps to an
abelian sheaf on the small étale site of `X`. Then `ψ` presents `𝓑` as the colimit
`colim f_i⁻¹F_i` as soon as, for every object `V₀` of the small étale site of a stage `X_{i₀}`
with quasi-compact and quasi-separated underlying scheme, the sections `𝓑(V₀ ×_{X_{i₀}} X)` are
the colimit of the sections `F_k(V₀ ×_{X_{i₀}} X_k)`, elementwise: every section of `𝓑` comes
from a stage, and a section of a stage which vanishes in `𝓑` vanishes at a later stage.

Indeed, the comparison `κ : colim f_i⁻¹F_i ⟶ 𝓑` is then bijective on the sections over every
such `V₀ ×_{X_{i₀}} X`, by the degree zero case of [Stacks, Tag 09YQ] for the colimit
(`Stacks.EtaleCohomology.EtaleSheafSystem.exists_pushforwardLeg_apply_eq`); these objects cover
every object of the small étale site of `X`
(`AlgebraicGeometry.exists_isAffineOpen_isPullback_etale_of_isLimit`), so `κ` is locally
bijective, hence an isomorphism.

## Main results

* `Stacks.EtaleCohomology.EtaleSheafSystem.pushforwardLeg_comp` — the legs of a cocone followed
  by a map have as pushed-forward legs the pushed-forward legs followed by its direct image.
* `Stacks.EtaleCohomology.EtaleSheafSystem.isPullbackColimitPresentation_of_forall_exists` — the
  criterion.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} (c : Cone D)

/-- **The pushed-forward legs of a cocone followed by a map.** For a family `ι_i : f_i⁻¹F_i ⟶ 𝓖`
and a map `κ : 𝓖 ⟶ 𝓖'`, the pushed-forward legs of the family `ι_i ≫ κ` are those of `ι`
followed by the direct image of `κ`. -/
lemma EtaleSheafSystem.pushforwardLeg_comp (F : EtaleSheafSystem D Ab.{u + 1})
    {𝓖 𝓖' : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓖) (κ : 𝓖 ⟶ 𝓖')
    {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) :
    F.pushforwardLeg c (fun i => ι i ≫ κ) a =
      F.pushforwardLeg c ι a ≫ (smallEtalePushforwardAb (c.π.app i₀)).map κ := by
  rw [← F.pushforwardUnit_comp_map c (fun i => ι i ≫ κ) a, ← F.pushforwardUnit_comp_map c ι a,
    Functor.map_comp, Category.assoc]

variable [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
  {c} (hc : IsLimit c)

include hc in
/-- **The objects of the small étale site of the limit coming from quasi-compact quasi-separated
objects of the stages cover.** Every point of an object `U` of the small étale site of the limit
lies in the image of a morphism to `U` from the base change of an object of the small étale
site of a stage with quasi-compact and quasi-separated underlying scheme. -/
theorem exists_smallEtaleBaseChange_hom_mem_range (U : c.pt.Etale) (x : U.left) :
    ∃ (i₀ : Iᵒᵖ) (V₀ : (D.obj i₀).Etale) (_ : CompactSpace V₀.left)
      (_ : QuasiSeparatedSpace V₀.left) (f : (smallEtaleBaseChange (c.π.app i₀)).obj V₀ ⟶ U),
      x ∈ Set.range f.left := by
  obtain ⟨U'', -, hxU'', j, Y, p, θ, hp, hYc, hYs, hθ⟩ :=
    exists_isAffineOpen_isPullback_etale_of_isLimit D c hc U.hom x
  let V₀ : (D.obj j).Etale := Scheme.Etale.mk p
  let U' : c.pt.Etale := Scheme.Etale.mk (U''.ι ≫ U.hom)
  let e : U' ≅ (smallEtaleBaseChange (c.π.app j)).obj V₀ :=
    MorphismProperty.Comma.isoMk hθ.isoPullback (Iso.refl _)
      (hθ.isoPullback_hom_snd.trans (Category.comp_id _).symm)
  let f : U' ⟶ U := MorphismProperty.Over.homMk U''.ι rfl trivial
  refine ⟨j, V₀, hYc, hYs, e.inv ≫ f, ?_⟩
  exact ⟨e.hom.left ⟨x, hxU''⟩, congrArg (fun φ => φ.left ⟨x, hxU''⟩) (e.hom_inv_id_assoc f)⟩

variable (F : EtaleSheafSystem D Ab.{u + 1}) {𝓑 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
  (ψ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓑)
  (hψ : LimitHigherDirectImage.IsPullbackCocone c F ψ)

include hc hψ in
/-- **A compatible family presents the colimit as soon as it does so elementwise on the
quasi-compact quasi-separated objects of the stages.** Let `ψ_i : f_i⁻¹F_i ⟶ 𝓑` be compatible
with the transition maps. Suppose that for every object `V₀` of the small étale site of a stage
`X_{i₀}` with quasi-compact and quasi-separated underlying scheme, every section of `𝓑` over
`V₀ ×_{X_{i₀}} X` is the image under a pushed-forward leg of a section of some `F_k` over
`V₀ ×_{X_{i₀}} X_k`, and a section of `F_k` over `V₀ ×_{X_{i₀}} X_k` whose image vanishes already
vanishes at a later stage. Then `ψ` presents `𝓑 = colim f_i⁻¹F_i`. -/
theorem EtaleSheafSystem.isPullbackColimitPresentation_of_forall_exists
    (hsurj : ∀ (i₀ : Iᵒᵖ) (V₀ : (D.obj i₀).Etale) [CompactSpace V₀.left]
      [QuasiSeparatedSpace V₀.left]
      (s : ToType (𝓑.obj.obj (op ((smallEtaleBaseChange (c.π.app i₀)).obj V₀)))),
      ∃ (k : Iᵒᵖ) (a : k ⟶ i₀)
        (x : ToType ((F.obj k).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀)))),
        (F.pushforwardLeg c ψ a).hom.app (op V₀) x = s)
    (hinj : ∀ (i₀ : Iᵒᵖ) (V₀ : (D.obj i₀).Etale) [CompactSpace V₀.left]
      [QuasiSeparatedSpace V₀.left] {k : Iᵒᵖ} (a : k ⟶ i₀)
      (x : ToType ((F.obj k).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀)))),
      (F.pushforwardLeg c ψ a).hom.app (op V₀) x = 0 →
      ∃ (l : Iᵒᵖ) (b : l ⟶ k), (F.pushforwardTransition b a).hom.app (op V₀) x = 0) :
    LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓑 F ψ := by
  obtain ⟨C, ιC, hιC, hC⟩ := LimitHigherDirectImage.exists_isPullbackColimitPresentation
    (cX := c) F
  have hψ' : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), ((conePullbackComp c a).inv.app (F.obj j) ≫
      (smallEtalePullbackAb (c.π.app i)).map (F.map a)) ≫ ψ i = ψ j :=
    fun a => (Category.assoc _ _ _).trans (hψ a)
  let κ : C ⟶ 𝓑 := hC.isSystemColimit.desc ψ hψ'
  have hκ : ∀ i, ιC i ≫ κ = ψ i := hC.isSystemColimit.fac ψ hψ'
  have hleg : ∀ {k i₀ : Iᵒᵖ} (a : k ⟶ i₀),
      F.pushforwardLeg c ψ a =
        F.pushforwardLeg c ιC a ≫ (smallEtalePushforwardAb (c.π.app i₀)).map κ :=
    fun a => by rw [← F.pushforwardLeg_comp c ιC κ a, funext hκ]
  -- bijectivity on the base changes of quasi-compact quasi-separated objects of the stages
  have hgood : ∀ (i₀ : Iᵒᵖ) (V₀ : (D.obj i₀).Etale) [CompactSpace V₀.left]
      [QuasiSeparatedSpace V₀.left],
      Function.Bijective (κ.hom.app (op ((smallEtaleBaseChange (c.π.app i₀)).obj V₀))) := by
    intro i₀ V₀ _ _
    refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, fun s => ?_⟩
    · obtain ⟨k, a, x, rfl⟩ := F.exists_pushforwardLeg_apply_eq c hc ιC hιC hC V₀ y
      obtain ⟨l, b, hb⟩ := hinj i₀ V₀ a x (by rwa [hleg a])
      rw [← F.pushforwardTransition_comp_pushforwardLeg c ιC hιC b a]
      show (F.pushforwardLeg c ιC (b ≫ a)).hom.app (op V₀)
        ((F.pushforwardTransition b a).hom.app (op V₀) x) = 0
      rw [hb, map_zero]
    · obtain ⟨k, a, x, rfl⟩ := hsurj i₀ V₀ s
      exact ⟨(F.pushforwardLeg c ιC a).hom.app (op V₀) x, by rw [hleg a]; rfl⟩
  -- these base changes cover, so the comparison is locally bijective, hence an isomorphism
  have hcov : ∀ {U : c.pt.Etale} (S : Sieve U), (∀ (i₀ : Iᵒᵖ) (V₀ : (D.obj i₀).Etale)
      [CompactSpace V₀.left] [QuasiSeparatedSpace V₀.left]
      (f : (smallEtaleBaseChange (c.π.app i₀)).obj V₀ ⟶ U), S f) →
      S ∈ smallEtaleTopology c.pt U := by
    intro U S hS
    choose i₀ V₀ hc₁ hc₂ f hf using exists_smallEtaleBaseChange_hom_mem_range hc U
    refine (smallEtaleTopology c.pt).superset_covering ?_
      ((Scheme.ofArrows_mem_smallEtaleTopology_iff f).2
        (Set.eq_univ_of_forall fun z => Set.mem_iUnion.2 ⟨z, hf z⟩))
    refine (Sieve.generate_le_iff _ _).2 ?_
    rintro V g ⟨z⟩
    have := hc₁ z
    have := hc₂ z
    exact hS _ _ _
  have hiso : IsIso κ := by
    refine (Sheaf.isLocallyBijective_iff_isIso κ).mp ⟨⟨fun x y hxy => hcov _ fun i₀ V₀ _ _ f =>
      (hgood i₀ V₀).1 ?_⟩, ⟨fun s => hcov _ fun i₀ V₀ _ _ f => (hgood i₀ V₀).2 _⟩⟩
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    exact congrArg _ hxy
  exact .of_isSystemColimit ((hC.isSystemColimit.of_iso (asIso κ)).congr_legs hκ)

end Stacks.EtaleCohomology
