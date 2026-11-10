module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import Mathlib.CategoryTheory.Sites.Sieves.Functoriality
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.KernelPairCoequalizer

/-!
# A surjective étale atlas presents a sheaf as the quotient of its kernel pair

Let `F` be a sheaf on the big fppf site over `S` and let `f : h_U ⟶ F` be a representable,
surjective, étale morphism from an object `U` of the site — an *atlas* for `F`. Since `f` is
representable, its kernel pair is representable too: there is an object `R` of the site and
morphisms `s, t : R ⟶ U` with `h_R = h_U ×_F h_U`. This file proves that `f` then exhibits `F`
as the quotient of `U` by `R` in the category of sheaves, i.e. `F` has the universal property
of `U/R`.

The two ingredients are that `f` is surjective as a map of sheaves — the base change of `f`
along any section of `F` is a surjective étale morphism of schemes, hence generates a covering
sieve, along which the section lifts — and that `h_R` realises the kernel pair of `f`
pointwise, which is immediate from the Yoneda lemma. The universal property is then
`CategoryTheory.Sheaf.nonempty_isColimitCoforkOfKernelPair`.

That a surjective étale morphism of the bounded category of schemes of a big fppf site
generates a covering sieve of the fppf topology is the first thing proved below; it needs a
terminal object in that category, which is the empty-shape companion of the Tag 021U
instance for fibre products.

Consequently Tag 0BGQ, that a sheaf with such an atlas is an algebraic space, reduces to the
quotient theorem Tag 02WW: once the quotient sheaf `U/R` of an étale equivalence relation is
known to be an algebraic space, `F` is isomorphic to it by the two universal properties and so
is an algebraic space as well. That reduction is
`AlgebraicGeometry.isAlgebraicSpace_of_surjective_etale_atlas_of_isAlgebraicSpace_quotient`;
the missing input is stated there as a hypothesis, since it is Tag 02WW and is not available.

## Main results

* `AlgebraicGeometry.Space.schemeCutoff_isClosedUnderLimitsOfShape_empty` is what makes
  `CategoryTheory.Limits.HasTerminal B.Schemes` synthesise.
* `AlgebraicGeometry.Space.singleton_mem_bigFppf_topology`, with its `BigFppfSite`-namespace
  spelling `AlgebraicGeometry.BigFppfSite.generate_singleton_mem_topology`: a surjective étale
  morphism of a big fppf site generates a covering sieve.
* `AlgebraicGeometry.isLocallySurjective_of_surjective_etale`: a representable surjective étale
  morphism of presheaves is locally surjective, the sheaf-theoretic surjectivity of Tag 05VM.
* `AlgebraicGeometry.existsUnique_desc_of_surjective_etale_atlas`: a sheaf with a surjective
  étale atlas is the quotient of the atlas by its kernel pair.
* `AlgebraicGeometry.isAlgebraicSpace_of_iso`: being an algebraic space is invariant under
  isomorphism of presheaves.
* `AlgebraicGeometry.isAlgebraicSpace_of_surjective_etale_atlas_of_isAlgebraicSpace_quotient`:
  Tag 0BGQ, granted the quotient theorem Tag 02WW.

## Implementation notes

`schemeCutoff_isClosedUnderLimitsOfShape_empty` is the empty-shape companion of the 021U
instance `AlgebraicGeometry.schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan`
(`Topologies/Fppf/FibreProducts.lean`), and belongs beside it. It is `public` because without
it `CategoryTheory.Limits.HasTerminal B.Schemes` does not synthesise anywhere in the
repository, whereas `HasPullbacks B.Schemes` already does from the 021U instance.
`HasFiniteLimits B.Schemes` still does *not* synthesise from the two: Mathlib keeps
`hasFiniteLimits_of_hasTerminal_and_pullbacks` a theorem rather than an instance, so a
consumer wanting finite limits must supply that term explicitly.

Local surjectivity is Mathlib's `CategoryTheory.Presheaf.IsLocallySurjective`, whose covering
sieve for a section is `CategoryTheory.Presheaf.imageSieve`; the sieve produced here, generated
by the base change of the atlas, refines it.

The descent of a cofork along a locally surjective map of sheaves of sets is taken from
`StacksFrontier/CategoryTheory/Sites/KernelPairCoequalizer.lean`, which states it for sheaves of
`Type w` on a site `C : Type u` with `Category.{v} C` and all three universes free; the fppf
site over `S` is a slice of a full subcategory of `Scheme.{u}`, hence lives in `Type (u + 1)`
with morphisms in `Type u`, and its sheaves of interest take values in `Type u`, which that
generality covers.

The universal property is stated for presheaf morphisms rather than for morphisms of the
category of sheaves, so that no bundling of `F` as an object of `Sheaf` appears in any
statement; the bundling happens inside the proofs, where the generic coequalizer criterion
needs it.

`AlgebraicGeometry.isAlgebraicSpace_of_iso` takes its hypothesis on the **target** of the
isomorphism. `AlgebraicGeometry.Space.isAlgebraicSpace_of_iso`, in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/RepresentableByAlgebraicSpaces.lean`, is the
same transport with the hypothesis on the **source**; the two are interderivable by
`CategoryTheory.Iso.symm` and both are kept because consumers of each are phrased against its
orientation. Because the second lives in a deeper namespace it shadows this one in files
inside `namespace AlgebraicGeometry.Space` which see it, so a use of this orientation there
must be written out as `AlgebraicGeometry.isAlgebraicSpace_of_iso`.

Stacks 0262 itself — the kernel pair of a surjective étale atlas as an étale equivalence
relation, and its quotient in fppf sheaves — is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Presentation/KernelPair.lean`.

## References

* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 0BGQ](https://stacks.math.columbia.edu/tag/0BGQ)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Covering sieves generated by a surjective étale morphism of the site -/

/-- The terminal scheme has size `ℵ₀`, hence lies below the cutoff of any big fppf site. -/
private theorem terminal_size_lt (B : BigFppfSite.{u}) :
    (⊤_ Scheme.{u}).size < B.cutoff := by
  have e : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    IsTerminal.uniqueUpToIso terminalIsTerminal specULiftZIsTerminal
  have hsize : (⊤_ Scheme.{u}).size = Cardinal.aleph0 := by
    calc
      (⊤_ Scheme.{u}).size = (Spec (CommRingCat.of (ULift.{u} ℤ))).size := Scheme.size_congr e
      _ = max Cardinal.aleph0 (Cardinal.mk (ULift.{u} ℤ)) :=
        Scheme.size_Spec (CommRingCat.of (ULift.{u} ℤ))
      _ = Cardinal.aleph0 := by simp
  exact hsize ▸ B.aleph0_lt_cutoff

/-- The schemes below the cutoff of a big fppf site are closed under limits of empty
shape, i.e. contain a terminal object. -/
public instance schemeCutoff_isClosedUnderLimitsOfShape_empty
    (B : BigFppfSite.{u}) {J : Type*} [Category J] [IsEmpty J] :
    ObjectProperty.IsClosedUnderLimitsOfShape (schemeSizeBelow B.cutoff) J := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, _⟩
  have hterm : IsTerminal (limit F) :=
    (isLimitEquivIsTerminalOfIsEmpty Scheme (J := J) (F := F) (limit.cone F))
      (limit.isLimit F)
  change (limit F).size < B.cutoff
  rw [Scheme.size_congr (hterm.uniqueUpToIso terminalIsTerminal)]
  exact terminal_size_lt B

/-- The underlying category of a big fppf site has a terminal object. -/
public instance schemeCutoff_hasTerminal (B : BigFppfSite.{u}) :
    HasTerminal B.Schemes := inferInstance

/-- The underlying category of a big fppf site has fibre products. -/
public theorem schemeCutoff_hasPullbacks (B : BigFppfSite.{u}) :
    HasPullbacks B.Schemes := inferInstance

attribute [local instance] schemeCutoff_hasPullbacks

/-- A surjective étale morphism of a big fppf site generates a covering sieve. -/
public theorem singleton_mem_bigFppf_topology
    (B : BigFppfSite.{u}) {X Y : B.Schemes} (g : Y ⟶ X)
    (hs : Surjective (B.inclusion.map g)) (he : Etale (B.inclusion.map g)) :
    Sieve.generate (Presieve.singleton g) ∈ B.topology X := by
  have hEt : Presieve.singleton (B.inclusion.map g) ∈
      Scheme.etalePrecoverage (B.inclusion.obj X) := by
    let : Surjective (B.inclusion.map g) := hs
    exact (Scheme.singleton_mem_precoverage_iff (@Etale.{u} : MorphismProperty Scheme.{u})
      (B.inclusion.map g)).2 ⟨Scheme.Hom.surjective _, he⟩
  have hE : IsFppfCovering (⟨X, PreZeroHypercover.singleton g⟩ : Covering B.Schemes) := by
    change (PreZeroHypercover.singleton g).presieve₀.map B.inclusion ∈
      Scheme.fppfPrecoverage (B.inclusion.obj X)
    simpa only [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton] using
      Scheme.etalePrecoverage_le_fppfPrecoverage _ hEt
  obtain ⟨E', hE', hEquiv⟩ := B.fppf_has_representative _ hE
  have hpre : (PreZeroHypercover.singleton g).presieve₀ ∈ B.precoverage X := by
    obtain ⟨hX, hComb⟩ := hEquiv
    cases hX
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb]
    exact ⟨E'.2, rfl, hE'⟩
  simpa [PreZeroHypercover.presieve₀_singleton] using
    Precoverage.generate_mem_toGrothendieck hpre

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

/-- A morphism of a big fppf site which is surjective and étale as a morphism of schemes
generates a covering sieve.

This is `AlgebraicGeometry.Space.singleton_mem_bigFppf_topology`, spelled in the
`AlgebraicGeometry.BigFppfSite` namespace so that it is available by dot notation on the
site. -/
theorem BigFppfSite.generate_singleton_mem_topology (B : BigFppfSite.{u}) {X Y : B.Schemes}
    (f : Y ⟶ X) (hs : Surjective (B.inclusion.map f)) (he : Etale (B.inclusion.map f)) :
    Sieve.generate (Presieve.singleton f) ∈ B.topology X :=
  Space.singleton_mem_bigFppf_topology B f hs he

/-- **Stacks 05VM** for a surjective étale morphism: a representable, surjective, étale
morphism of presheaves on the big fppf site over `S` is locally surjective, i.e. surjective as
a map of sheaves. -/
theorem isLocallySurjective_of_surjective_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) f)
    (hetale : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) f) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f := by
  constructor
  intro T ξ
  let hrep := hsurj.1
  let g : yoneda.obj T ⟶ F := yonedaEquiv.symm ξ
  let P := hrep.pullback g
  let q := hrep.snd g
  let fst := hrep.fst g
  let α : P ⟶ U := yoneda.preimage fst
  have hpb := hrep.isPullback g
  have hqSurj : Surjective ((BigFppfOver.toScheme B S hS).map q) := hsurj.2 g fst q hpb
  have hqEtale : Etale ((BigFppfOver.toScheme B S hS).map q) := hetale.2 g fst q hpb
  let q₀ := (BigFppfOver.forget B S hS).map q
  have hbase : Sieve.generate (Presieve.singleton q₀) ∈ B.topology T.left :=
    B.generate_singleton_mem_topology q₀ hqSurj hqEtale
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (B.topology.overEquiv_symm_mem_over T _ hbase)
  intro W k hk
  obtain ⟨V, a₀, b₀, ⟨⟩, hfac₀⟩ : Sieve.generate (Presieve.singleton q₀) k.left := by
    simpa using hk
  let a : W ⟶ P := Over.homMk a₀ (by
    calc
      a₀ ≫ P.hom = a₀ ≫ q.left ≫ T.hom := by rw [← Over.w q]
      _ = (a₀ ≫ q₀) ≫ T.hom := by rw [← Category.assoc]; rfl
      _ = k.left ≫ T.hom := by rw [hfac₀]
      _ = W.hom := Over.w k)
  have hak : a ≫ q = k := Over.OverMorphism.ext hfac₀
  refine ⟨yonedaEquiv (yoneda.map (a ≫ α)), ?_⟩
  change f.app (op W) (yonedaEquiv (yoneda.map (a ≫ α))) = F.map k.op ξ
  rw [← yonedaEquiv_comp]
  have hξ : yonedaEquiv g = ξ := yonedaEquiv.apply_symm_apply ξ
  rw [← hξ, yonedaEquiv_naturality]
  apply congrArg yonedaEquiv
  calc
    yoneda.map (a ≫ α) ≫ f = yoneda.map a ≫ yoneda.map α ≫ f := by
      simp [Functor.map_comp, Category.assoc]
    _ = yoneda.map a ≫ fst ≫ f := by simp [α]
    _ = yoneda.map a ≫ yoneda.map q ≫ g := by rw [hpb.w]
    _ = yoneda.map (a ≫ q) ≫ g := by simp [Functor.map_comp, Category.assoc]
    _ = yoneda.map k ≫ g := by rw [hak]

/-- A sheaf on the big fppf site over `S` with a representable, surjective, étale atlas
`f : h_U ⟶ F` is the quotient of `U` by the kernel pair `R` of `f`: every morphism from `h_U`
to a sheaf which identifies the two projections of `R` factors uniquely through `f`. -/
theorem existsUnique_desc_of_surjective_etale_atlas
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {U R : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F) {s t : R ⟶ U}
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) f)
    (hetale : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) f)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (k : yoneda.obj U ⟶ G) (hk : yoneda.map s ≫ k = yoneda.map t ≫ k) :
    ∃! d : F ⟶ G, f ≫ d = k := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : J.Subcanonical := inferInstanceAs (B.topology.over (B.obj hS)).Subcanonical
  have hyon : ∀ X : BigFppfOver B S hS, Presheaf.IsSheaf J (yoneda.obj X) := fun X ↦
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hyon R⟩
  let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hyon U⟩
  let FF : Sheaf J (Type u) := ⟨F, hF⟩
  let GF : Sheaf J (Type u) := ⟨G, hG⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let ff : UF ⟶ FF := ⟨f⟩
  let kf : UF ⟶ GF := ⟨k⟩
  have wF : sf ≫ ff = tf ≫ ff := Sheaf.hom_ext hR.w
  have wG : sf ≫ kf = tf ≫ kf := Sheaf.hom_ext hk
  have hker : ∀ ⦃T : BigFppfOver B S hS⦄ (x y : UF.obj.obj (op T)),
      ff.hom.app (op T) x = ff.hom.app (op T) y →
      ∃ r : RF.obj.obj (op T),
        sf.hom.app (op T) r = x ∧ tf.hom.app (op T) r = y := by
    intro T x y hxy
    have hxy' : yoneda.map x ≫ f = yoneda.map y ≫ f := by
      apply yonedaEquiv.injective
      simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using hxy
    let l := hR.lift (yoneda.map x) (yoneda.map y) hxy'
    have key : ∀ (m : yoneda.obj R ⟶ yoneda.obj U) (z : UF.obj.obj (op T)),
        l ≫ m = yoneda.map z → m.app (op T) (yonedaEquiv l) = z := fun m z h ↦ by
      rw [← yonedaEquiv_comp, ← yonedaEquiv_yoneda_map z]
      exact congrArg yonedaEquiv h
    exact ⟨yonedaEquiv l, key _ x (hR.lift_fst _ _ hxy'), key _ y (hR.lift_snd _ _ hxy')⟩
  have hcolim : IsColimit (Cofork.ofπ ff wF) :=
    Sheaf.isColimitCoforkOfKernelPair sf tf ff wF hker
      (isLocallySurjective_of_surjective_etale B S hS f hsurj hetale)
  refine ⟨(hcolim.desc (Cofork.ofπ kf wG)).hom, ?_, ?_⟩
  · have h : ff ≫ hcolim.desc (Cofork.ofπ kf wG) = kf := by
      simpa only [Cofork.π_ofπ] using
        Cofork.IsColimit.π_desc hcolim (t := Cofork.ofπ kf wG)
    exact congrArg (fun η : UF ⟶ GF ↦ η.hom) h
  · intro d hd
    have hdd : ff ≫ (⟨d⟩ : FF ⟶ GF) = kf := Sheaf.hom_ext hd
    have h : (⟨d⟩ : FF ⟶ GF) = hcolim.desc (Cofork.ofπ kf wG) :=
      Cofork.IsColimit.hom_ext hcolim (by
        rw [Cofork.IsColimit.π_desc hcolim]
        simpa only [Cofork.π_ofπ] using hdd)
    exact congrArg (fun η : FF ⟶ GF ↦ η.hom) h

/-- Being an algebraic space over `S` is invariant under isomorphism of presheaves. -/
theorem isAlgebraicSpace_of_iso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) (hG : IsAlgebraicSpace B S hS G) :
    IsAlgebraicSpace B S hS F := by
  refine ⟨(Presheaf.isSheaf_of_iso_iff
    (J := BigFppfOver.topology B S hS) e).mpr hG.isSheaf, ?_, ?_⟩
  · exact (MorphismProperty.cancel_right_of_respectsIso (P := yoneda.relativelyRepresentable)
      (diag F) (prod.map e.hom e.hom)).mp (by simpa only [prod.diag_map] using
      ((MorphismProperty.cancel_left_of_respectsIso (P := yoneda.relativelyRepresentable)
      e.hom (diag G)).mpr hG.diagonal_representable))
  · obtain ⟨U, f, hfs, hfe⟩ := hG.exists_atlas
    exact ⟨U, f ≫ e.inv,
      MorphismProperty.RespectsIso.postcomp _ e.inv f hfs,
      MorphismProperty.RespectsIso.postcomp _ e.inv f hfe⟩

/-- **Stacks 0BGQ**, reduced to the quotient theorem **Stacks 02WW**. A sheaf `F` on the big
fppf site over `S` with a representable, surjective, étale atlas `f : h_U ⟶ F` whose kernel
pair is `R` is an algebraic space, provided the quotient of `U` by `R` is one: the hypothesis
asks for a sheaf `Q` which is an algebraic space together with a morphism `q : h_U ⟶ Q` having
the universal property of `U/R`. Tag 02WW supplies exactly that for the quotient sheaf of an
étale equivalence relation, and is the only missing input. -/
theorem isAlgebraicSpace_of_surjective_etale_atlas_of_isAlgebraicSpace_quotient
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {U R : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F) {s t : R ⟶ U}
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) f)
    (hetale : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) f)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
    (q : yoneda.obj U ⟶ Q) (wq : yoneda.map s ≫ q = yoneda.map t ≫ q)
    (hquniv : ∀ G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) G →
      ∀ k : yoneda.obj U ⟶ G, yoneda.map s ≫ k = yoneda.map t ≫ k →
        ∃! d : Q ⟶ G, q ≫ d = k) :
    IsAlgebraicSpace B S hS F := by
  obtain ⟨m, hm, -⟩ :=
    existsUnique_desc_of_surjective_etale_atlas B S hS hF f hR hsurj hetale hQ.isSheaf q wq
  obtain ⟨d, hd, -⟩ := hquniv F hF f hR.w
  refine isAlgebraicSpace_of_iso B S hS ⟨m, d, ?_, ?_⟩ hQ
  · exact (existsUnique_desc_of_surjective_etale_atlas B S hS hF f hR hsurj hetale hF f
      hR.w).unique (by rw [← Category.assoc, hm, hd]) (Category.comp_id f)
  · exact (hquniv Q hQ.isSheaf q wq).unique (by rw [← Category.assoc, hd, hm])
      (Category.comp_id q)

end AlgebraicGeometry

end
