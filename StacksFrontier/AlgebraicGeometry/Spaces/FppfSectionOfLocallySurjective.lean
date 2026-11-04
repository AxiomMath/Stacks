module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Size.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds
import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# A sheaf with local sections has a section over one fppf covering morphism

Let `S` be a scheme of a big fppf site, let `U` be an object of that site and let `F` be a
sheaf on the site with a morphism `a : F ⟶ h_U` which is locally surjective, that is, `F` has
sections over a covering of `U`. Then there is a single object `V` of the site and a single
morphism `f : V ⟶ U` of the site, flat, locally of finite presentation and surjective, over
which `F` has a section.

## Main results

* `AlgebraicGeometry.Space.exists_coproduct_of_contains`: a family in the site whose coproduct
  of underlying schemes is of the site's size has a coproduct in the site.
* `AlgebraicGeometry.Space.coproduct_cover`: the summands of such a coproduct cover it by
  monomorphisms with empty pairwise intersections.
* `AlgebraicGeometry.Space.exists_fppf_section`: the statement above.

## References

* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 0AHL](https://stacks.math.columbia.edu/tag/0AHL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {𝒞 : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}

/-- A family in the big fppf site over `S` whose coproduct of underlying schemes is again of the
site's size is realized by an object of the site, together with the comparison isomorphism. -/
public lemma exists_coproduct_of_contains
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} (U : I → AlgebraicGeometry.BigFppfOver B S hS)
    (hU : B.Contains (∐ (fun i =>
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (U i)))) :
    ∃ (V : AlgebraicGeometry.BigFppfOver B S hS) (j : ∀ i, U i ⟶ V),
      Nonempty (IsColimit (Cofan.mk V j)) ∧
      ∃ e : (∐ (fun i => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (U i))) ≅
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V,
        ∀ i, Sigma.ι _ i ≫ e.hom = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (j i) := by
  let X := fun i => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (U i)
  let Vobj := B.obj hU
  let vmap : Vobj ⟶ B.obj hS := B.inclusion.preimage
    (show B.inclusion.obj Vobj ⟶ B.inclusion.obj (B.obj hS) from
      Sigma.desc (fun i => B.inclusion.map (U i).hom))
  have hv : B.inclusion.map vmap = Sigma.desc (fun i => B.inclusion.map (U i).hom) :=
    B.inclusion.map_preimage _
  let V : AlgebraicGeometry.BigFppfOver B S hS := Over.mk vmap
  let ιp (i : I) : (U i).left ⟶ Vobj := B.inclusion.preimage
    (show B.inclusion.obj (U i).left ⟶ B.inclusion.obj Vobj from Sigma.ι X i)
  have hι (i : I) : B.inclusion.map (ιp i) = Sigma.ι X i := B.inclusion.map_preimage _
  have hw (i : I) : ιp i ≫ vmap = (U i).hom := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, hι, hv, Sigma.ι_desc]
  let j : ∀ i, U i ⟶ V := fun i => Over.homMk (ιp i) (hw i)
  let m (c : Cofan U) : Vobj ⟶ c.pt.left :=
    B.inclusion.preimage (Sigma.desc (fun i => B.inclusion.map (c.inj i).left))
  have hm (c : Cofan U) (i : I) : Sigma.ι X i ≫ B.inclusion.map (m c) =
      B.inclusion.map (c.inj i).left := by
    simp only [m, Functor.map_preimage, Sigma.ι_desc]
  refine ⟨V, j, ⟨Cofan.IsColimit.mk _ (fun c => ?_) ?_ ?_⟩, Iso.refl _, ?_⟩
  · refine Over.homMk (m c) ?_
    apply B.inclusion.map_injective
    apply Sigma.hom_ext
    intro i
    rw [Functor.map_comp, ← Category.assoc, hm, ← Functor.map_comp, Over.w]
    change _ = _ ≫ B.inclusion.map vmap
    rw [hv, Sigma.ι_desc]
  · intro c i
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map (ιp i) ≫ B.inclusion.map (m c) = _
    rw [hι, hm]
  · intro c f hf
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    apply Sigma.hom_ext
    intro i
    change _ = _ ≫ B.inclusion.map (m c)
    rw [hm]
    have hi := congrArg (fun g : U i ⟶ c.pt => B.inclusion.map g.left) (hf i)
    change B.inclusion.map (ιp i ≫ f.left) = _ at hi
    rwa [Functor.map_comp, hι] at hi
  · intro i
    exact (Category.comp_id _).trans (hι i).symm

/-- The summands of a coproduct inside the big fppf site over `S` form a covering by
monomorphisms with empty pairwise intersections. -/
public lemma coproduct_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} (X : I → AlgebraicGeometry.BigFppfOver B S hS)
    (V : AlgebraicGeometry.BigFppfOver B S hS) (j : ∀ i, X i ⟶ V)
    (e : (∐ (fun i => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (X i))) ≅
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V)
    (he : ∀ i, Sigma.ι _ i ≫ e.hom = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (j i)) :
    (∀ i, Mono (j i)) ∧
    Sieve.ofArrows X j ∈ AlgebraicGeometry.BigFppfOver.topology B S hS V ∧
    (∀ {i k}, i ≠ k → ∀ {Y : AlgebraicGeometry.BigFppfOver B S hS}
      (a : Y ⟶ X i) (b : Y ⟶ X k), a ≫ j i = b ≫ j k →
        ⊥ ∈ AlgebraicGeometry.BigFppfOver.topology B S hS Y) := by
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let A := fun i => T.obj (X i)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have : Mono (T.map (j i)) := by rw [← he i]; infer_instance
    exact T.mono_of_mono_map inferInstance
  · let E : PreZeroHypercover.{u + 1} V :=
      { I₀ := ULift.{u + 1} I, X := fun i => X i.down, f := fun i => j i.down }
    have hE : (E.map T).presieve₀ ∈ Scheme.fppfPrecoverage (T.obj V) := by
      rw [PreZeroHypercover.presieve₀, Scheme.fppfPrecoverage,
        Scheme.ofArrows_mem_precoverage_iff]
      constructor
      · intro t
        obtain ⟨t, rfl⟩ := e.hom.homeomorph.surjective t
        obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk A).surjective t
        refine ⟨ULift.up i, x, ?_⟩
        show T.map (j i) x = _
        rw [← he i, Scheme.Hom.comp_apply, sigmaMk_mk]
        rfl
      · intro i
        show Flat (T.map (j i.down)) ∧ LocallyOfFinitePresentation (T.map (j i.down))
        rw [← he i.down]
        constructor <;> infer_instance
    have hEq : E.sieve₀ = Sieve.ofArrows X j := by
      apply le_antisymm <;> rw [Sieve.generate_le_iff]
      · rintro Z f ⟨i⟩
        exact Sieve.ofArrows_mk X j i.down
      · rintro Z f ⟨i⟩
        exact E.sieve₀_f (ULift.up i)
    rw [← hEq]
    exact AlgebraicGeometry.Stack.sieve_mem_of_fppf B S hS E hE
  · intro i k hik Y a b hab
    have hh : T.map a ≫ Sigma.ι A i = T.map b ≫ Sigma.ι A k := by
      apply (cancel_mono e.hom).mp
      rw [Category.assoc, he i, Category.assoc, he k, ← T.map_comp, ← T.map_comp, hab]
    have : IsEmpty (T.obj Y) := isEmpty_of_commSq_sigmaι_of_ne ⟨hh⟩ hik
    exact AlgebraicGeometry.BigFppfOver.bot_mem_topology Y this

/-- If `F` is a sheaf on the big fppf site over `S` and `a : F ⟶ h_U` is locally surjective,
then there are an object `V` of the site and a flat, locally finitely presented, surjective
morphism `f : V ⟶ U` of the site such that `yoneda.map f` lifts along `a`. -/
public theorem exists_fppf_section
    {U : AlgebraicGeometry.BigFppfOver 𝒞 S hS}
    {F : (AlgebraicGeometry.BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS) F)
    (a : F ⟶ yoneda.obj U)
    (ha : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS) a) :
    ∃ (V : AlgebraicGeometry.BigFppfOver 𝒞 S hS) (f : V ⟶ U) (s : yoneda.obj V ⟶ F),
      s ≫ a = yoneda.map f ∧
      Flat ((AlgebraicGeometry.BigFppfOver.toScheme 𝒞 S hS).map f) ∧
      LocallyOfFinitePresentation ((AlgebraicGeometry.BigFppfOver.toScheme 𝒞 S hS).map f) ∧
      Surjective ((AlgebraicGeometry.BigFppfOver.toScheme 𝒞 S hS).map f) := by
  classical
  let J := AlgebraicGeometry.BigFppfOver.topology 𝒞 S hS
  let Ts := AlgebraicGeometry.BigFppfOver.toScheme 𝒞 S hS
  let := ha
  let R := Presheaf.imageSieve a (U := U) (𝟙 U)
  have hR : R ∈ J U := ha.imageSieve_mem (U := U) (𝟙 U)
  obtain ⟨E, hE, hle⟩ := exists_covering_refining_sieve 𝒞
    ((𝒞.topology.mem_over_iff R).mp hR)
  have hEambient : (E.map 𝒞.inclusion).presieve₀ ∈ Scheme.fppfPrecoverage
      (Ts.obj U) := by
    rw [PreZeroHypercover.presieve₀_map]
    exact Precoverage.mem_comap_iff.mp (𝒞.isFppfCovering_of_isCovering hE)
  have hfields := (Scheme.ofArrows_mem_precoverage_iff
    (P := @Flat ⊓ @LocallyOfFinitePresentation)).mp hEambient
  let C : FppfCovering (Ts.obj U) := {
    «ι» := E.I₀
    X i := 𝒞.inclusion.obj (E.X i)
    f i := 𝒞.inclusion.map (E.f i)
    flat i := (hfields.2 i).1
    lfp i := (hfields.2 i).2
    jointly_surjective := hfields.1 }
  obtain ⟨W, hWref, hWsize⟩ := exists_fppf_refinement_schemeSize_le (Ts.obj U) C
  have hWi i : 𝒞.Contains (W.X i) :=
    (Scheme.size_le_of_mono_locallyOfFinitePresentation (Sigma.ι W.X i)).trans
      hWsize |>.trans_lt U.left.property
  let Wi i : AlgebraicGeometry.BigFppfOver 𝒞 S hS :=
    Over.mk (𝒞.inclusion.preimage
      (show 𝒞.inclusion.obj (𝒞.obj (hWi i)) ⟶ 𝒞.inclusion.obj U.left from W.f i) ≫ U.hom)
  let wi i : Wi i ⟶ U := Over.homMk (𝒞.inclusion.preimage (W.f i))
  have hwi i : Ts.map (wi i) = W.f i := 𝒞.inclusion.map_preimage _
  have hmem i : R (wi i) := by
    obtain ⟨k, b, hb⟩ := hWref i
    let b' : (Wi i).left ⟶ E.X k := 𝒞.inclusion.preimage b
    have hb' : b' ≫ E.f k = (wi i).left := by
      apply 𝒞.inclusion.map_injective
      show 𝒞.inclusion.map (b' ≫ E.f k) =
        𝒞.inclusion.map
          (𝒞.inclusion.preimage (X := (Wi i).left) (Y := U.left) (W.f i))
      rw [Functor.map_comp, Functor.map_preimage]
      simpa only [b', Functor.map_preimage] using hb
    have hh := (Sieve.overEquiv U R).downward_closed
      (hle _ _ (E.presieve₀_f k)) b'
    rw [hb'] at hh
    exact (Sieve.overEquiv_iff R _).mp hh
  choose si hsi using hmem
  have hsum : 𝒞.Contains (∐ (fun i => Ts.obj (Wi i))) :=
    hWsize.trans_lt U.left.property
  obtain ⟨V, j, ⟨hjcol⟩, e, he⟩ := exists_coproduct_of_contains 𝒞 S hS Wi hsum
  obtain ⟨hm, hj, hd⟩ := coproduct_cover 𝒞 S hS Wi V j e he
  let f : V ⟶ U := hjcol.desc (Cofan.mk U wi)
  have hjf i : j i ≫ f = wi i := hjcol.fac (Cofan.mk U wi) ⟨i⟩
  let ss i : PUnit ⟶ F.obj (Opposite.op (Wi i)) := ↾fun _ => si i
  have hcompat : ∀ ⦃Y⦄ ⦃i k⦄ (b : Y ⟶ Wi i) (c : Y ⟶ Wi k),
      b ≫ j i = c ≫ j k → ss i ≫ F.map b.op = ss k ≫ F.map c.op := by
    intro Y i k b c hbc
    by_cases hik : i = k
    · subst k
      let := hm i
      rw [(cancel_mono (j i)).mp hbc]
    · exact hF.hom_ext_ofArrows (X := fun z : PEmpty.{u + 1} => z.elim) (fun z => z.elim)
        (by simpa [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty] using hd hik b c hbc)
        fun z => z.elim
  obtain ⟨s₀, hs₀, -⟩ := hF.existsUnique_amalgamation_ofArrows j hj ss hcompat
  let s := yonedaEquiv.symm (s₀ PUnit.unit)
  have hs i : yoneda.map (j i) ≫ s = yonedaEquiv.symm (si i) := by
    apply yonedaEquiv.injective
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact ConcreteCategory.congr_hom (hs₀ i) PUnit.unit
  have hsa : s ≫ a = yoneda.map f := by
    apply yonedaEquiv.injective
    apply hjcol.hom_ext
    rintro ⟨i⟩
    show (yoneda.obj U).map (j i).op (yonedaEquiv (s ≫ a)) =
      (yoneda.obj U).map (j i).op (yonedaEquiv (yoneda.map f))
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality, ← Category.assoc, hs, ← Functor.map_comp,
      hjf, yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
    simpa using hsi i
  have hef : e.hom ≫ Ts.map f = Sigma.desc W.f := Sigma.hom_ext _ _ fun i => by
    rw [← Category.assoc, he, ← Functor.map_comp, hjf, hwi, Sigma.ι_desc]
  have : ∀ i, Flat (W.f i) := W.flat
  have : ∀ i, LocallyOfFinitePresentation (W.f i) := W.lfp
  let : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
  let : MorphismProperty.RespectsIso (@Flat.{u}) :=
    (inferInstance : MorphismProperty.IsStableUnderBaseChange (@Flat.{u})).respectsIso
  let : MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) :=
    (inferInstance :
      MorphismProperty.IsStableUnderBaseChange (@LocallyOfFinitePresentation.{u})).respectsIso
  have hflat : Flat (e.hom ≫ Ts.map f) := by rw [hef]; infer_instance
  have hlfp : LocallyOfFinitePresentation (e.hom ≫ Ts.map f) := by
    rw [hef]
    exact IsZariskiLocalAtSource.sigmaDesc
      (P := @LocallyOfFinitePresentation.{u}) (fun i => W.lfp i)
  refine ⟨V, f, s, hsa, (MorphismProperty.cancel_left_of_respectsIso (@Flat.{u}) e.hom _).mp hflat,
    (MorphismProperty.cancel_left_of_respectsIso
      (@LocallyOfFinitePresentation.{u}) e.hom _).mp hlfp, ⟨fun x => ?_⟩⟩
  obtain ⟨i, y, hy⟩ := W.jointly_surjective x
  refine ⟨Ts.map (j i) y, ?_⟩
  show (Ts.map (j i) ≫ Ts.map f) y = x
  rwa [← Functor.map_comp, hjf, hwi]


end AlgebraicGeometry.Space

end
