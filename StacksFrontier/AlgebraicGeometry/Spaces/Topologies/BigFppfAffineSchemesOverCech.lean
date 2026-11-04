module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfAffineSchemesOverLimits
public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveSheaves
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFppfFaithfullyFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianModuleCech

/-!
# Čech cohomology of the base change sheaf on the affine schemes over an affine object

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `X` one of its objects and `V`
an object of `(Spaces/X)_fppf` identified with the algebraic space represented by an affine
scheme. On the affine schemes over `V` the base change presheaf `A ↦ 𝒪(A) ⊗ M` is a sheaf for
the topology induced from the big fppf site; the inclusions of a finite coproduct of affine
schemes over `V` cover it, so the base change presheaf takes finite coproducts to products.

## Main results

* `Scheme.ofArrows_mem_fppfPrecoverage_of_isColimit`: the inclusions of a
  finite coproduct of schemes form an fppf covering family.
* `BigFppfSpaceSite.AffineSchemesOver.ofArrows_mem_topology`: a family of
  affine schemes over `V` whose family of underlying schemes covers in the big fppf site of
  schemes covers in the induced topology.
* `BigFppfSpaceSite.AffineSchemesOver.extensiveTopology_le_topology`: the
  extensive topology is coarser than the induced topology.
* `BigFppfSpaceSite.AffineSchemesOver.faithfullyFlat_sigmaDesc`: the ring map to the coproduct of
  a finite fppf family is faithfully flat.
* `BigFppfSpaceSite.AffineSchemesOver.isZero_cechCohomology_baseChangePresheaf_succ`: the base
  change presheaf has vanishing positive Čech cohomology on finite fppf families (Stacks 03FJ on
  the affine schemes over `V`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **The inclusions of a finite coproduct of schemes form an fppf covering family.** -/
lemma Scheme.ofArrows_mem_fppfPrecoverage_of_isColimit {I : Type*} [Finite I]
    {X : I → Scheme.{u}} {c : Cofan X} (hc : IsColimit c) :
    Presieve.ofArrows X c.inj ∈ Scheme.fppfPrecoverage c.pt := by
  have hI : Small.{u} I := Countable.toSmall I
  have hι : ∀ i, IsOpenImmersion (c.inj i) := fun i => by
    have h := IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit
      (Discrete.functor X)) hc ⟨i⟩
    change colimit.ι (Discrete.functor X) ⟨i⟩ ≫ _ = c.inj i at h
    rw [← h]
    infer_instance
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun x => ?_, fun i => ⟨inferInstance, inferInstance⟩⟩
  obtain ⟨i, y, hy⟩ := Concrete.isColimit_exists_rep _
    (isColimitOfPreserves Scheme.forgetToTop hc) x
  exact ⟨i.as, y, hy⟩

/-- **A family of schemes over `S` whose underlying schemes form an fppf covering family
generates a covering sieve of the big fppf site over `S`.** -/
lemma BigFppfOver.ofArrows_mem_topology_of_mem_fppfPrecoverage (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {U : BigFppfOver B S hS} {I : Type*}
    {Y : I → BigFppfOver B S hS} (g : ∀ i, Y i ⟶ U)
    (h : Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (Y i))
        (fun i => (BigFppfOver.toScheme B S hS).map (g i)) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj U)) :
    Sieve.ofArrows Y g ∈ BigFppfOver.topology B S hS U := by
  rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  refine Precoverage.generate_mem_toGrothendieck ?_
  rwa [bigFppfPrecoverage_eq_comap B, Precoverage.mem_comap_iff, Presieve.map_ofArrows]

namespace BigFppfSpaceSite.AffineSchemesOver

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {X : T.Spaces} {V : BigFppfSpaceOver T X}

/-- **A family of affine schemes over `V` whose underlying schemes generate a covering sieve of
the big fppf site of schemes generates a covering sieve of the induced topology.** -/
theorem ofArrows_mem_topology {W : AffineSchemesOver T V} {I : Type*}
    {Y : I → AffineSchemesOver T V} (g : ∀ i, Y i ⟶ W)
    (hcov : Sieve.ofArrows (fun i => (Y i).obj.left) (fun i => (g i).hom.left) ∈
      BigFppfOver.topology T.schemeSite S T.scheme_mem W.obj.left) :
    Sieve.ofArrows Y g ∈ topology W := by
  let F := schemeSpaceFunctor T.schemeSite S T.scheme_mem
  have hsc := fppfSchemeToSpace_isSpecialCocontinuous T
  have := hsc.1
  have := hsc.2
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
  show Sieve.overEquiv _ (Sieve.overEquiv _
    ((Sieve.ofArrows Y g).functorPushforward (toSlice T V))) ∈ T.topology (F.obj W.obj.left)
  refine T.topology.superset_covering ?_ ((Functor.functorPushforward_mem_iff
    (BigFppfOver.topology T.schemeSite S T.scheme_mem) T.topology (G := F)).2 hcov)
  refine (Sieve.functor_galoisConnection F W.obj.left).l_le ?_
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  have hw : F.map (g i).hom.left ≫ W.obj.hom = (Y i).obj.hom := CostructuredArrow.w (g i).hom
  refine (Sieve.overEquiv_iff _ _).2 ((Sieve.overEquiv_iff _ _).2
    ⟨Y i, g i, Over.homMk (Over.homMk (𝟙 _) ?_) ?_, Sieve.ofArrows_mk Y g i, ?_⟩)
  · simp only [Category.id_comp]
    show (Y i).obj.hom ≫ V.hom = (F.map (g i).hom.left ≫ W.obj.hom) ≫ V.hom
    rw [hw]
  · exact Over.OverMorphism.ext (by simp)
  · exact Over.OverMorphism.ext (Over.OverMorphism.ext (Category.id_comp _).symm)

variable (V₀ : T.Schemes)
  (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
  (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ V.left)

/-- The functor taking an affine scheme over `V` to its underlying scheme. -/
noncomputable abbrev toSchemeFunctor : AffineSchemesOver T V ⥤ Scheme.{u} :=
  toAffineOverScheme V₀ e ⋙ (isAffineOverScheme T V₀).ι ⋙ Over.forget V₀ ⋙
    BigFppfOver.toScheme T.schemeSite S T.scheme_mem

include hV₀ in
/-- **The extensive topology on the affine schemes over `V` is coarser than the induced
topology**: the inclusions of a finite coproduct cover it. -/
theorem extensiveTopology_le_topology :
    letI := finitaryExtensive V₀ e hV₀
    extensiveTopology (AffineSchemesOver T V) ≤ topology := by
  let := finitaryExtensive V₀ e hV₀
  intro A R hR
  obtain ⟨I, hI, Y, f, ⟨hc⟩, hf⟩ :=
    (extensiveTopology.mem_sieves_iff_contains_colimit_cofan R).mp hR
  refine (topology (T := T) (V := V)).superset_covering (S := Sieve.ofArrows Y f)
    ((Sieve.generate_le_iff _ _).mpr (by rintro _ _ ⟨i⟩; exact hf i)) ?_
  exact ofArrows_mem_topology f (BigFppfOver.ofArrows_mem_topology_of_mem_fppfPrecoverage _ _ _ _
    (Scheme.ofArrows_mem_fppfPrecoverage_of_isColimit
      (isColimitCofanMkObjOfIsColimit (toSchemeFunctor V₀ e) _ f hc)))

include hV₀ e in
/-- **The base change presheaf takes finite coproducts of affine schemes over `V` to
products.** -/
theorem preservesFiniteProducts_baseChangePresheaf {W₀ : AffineSchemesOver T V}
    (hW₀ : IsTerminal W₀)
    (M : ModuleCat.{u + 1} ((ringPresheaf (T := T) (V := V)).obj (op W₀))) :
    PreservesFiniteProducts
      ((Stacks.TerminalBaseChange.baseChangePresheaf.{u + 1} (ringPresheaf (T := T) (V := V))
          hW₀).obj M).presheaf := by
  let := finitaryExtensive V₀ e hV₀
  rw [← Presheaf.isSheaf_iff_preservesFiniteProducts]
  exact fun E => Presieve.isSheaf_of_le _ (extensiveTopology_le_topology V₀ hV₀ e)
    (isSheaf_baseChangePresheaf hW₀ M E)

include e in
/-- **The ring of a fibre product over an affine scheme over `V` is the pushout of the rings.** -/
theorem isPushout_ringPresheaf_of_isLimit {A : AffineSchemesOver T V} {Y₁ Y₂ : Over A}
    (c : BinaryFan Y₁ Y₂) (hc : IsLimit c) :
    IsPushout (CommRingCat.ofHom ((ringPresheaf (T := T) (V := V)).map Y₁.hom.op).hom)
      (CommRingCat.ofHom ((ringPresheaf (T := T) (V := V)).map Y₂.hom.op).hom)
      (CommRingCat.ofHom ((ringPresheaf (T := T) (V := V)).map c.fst.left.op).hom)
      (CommRingCat.ofHom ((ringPresheaf (T := T) (V := V)).map c.snd.left.op).hom) :=
  isPushout_ringPresheaf ((Over.isPullback_of_binaryFan_isLimit c hc).map (toSchemeFunctor V₀ e))

attribute [local instance] ULift.algebra' in
include hV₀ in
/-- **The ring map to the coproduct of a finite fppf family of affine schemes over `V` is
faithfully flat.** -/
theorem faithfullyFlat_sigmaDesc {A : AffineSchemesOver T V} (E : PreZeroHypercover.{u + 1} A)
    [Finite E.I₀]
    (hfppf : Presieve.ofArrows
        (fun i => (BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj (E.X i).obj.left)
        (fun i => (BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map (E.f i).hom.left) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj A.obj.left)) :
    letI := finitaryExtensive V₀ e hV₀
    letI := ((ringPresheaf (T := T) (V := V)).map (Sigma.desc E.f).op).hom.toAlgebra
    Module.FaithfullyFlat ((ringPresheaf (T := T) (V := V)).obj (op A))
      ((ringPresheaf (T := T) (V := V)).obj (op (∐ E.X))) := by
  let := finitaryExtensive V₀ e hV₀
  let := ((ringPresheaf (T := T) (V := V)).map (Sigma.desc E.f).op).hom.toAlgebra
  let G := toSchemeFunctor V₀ e
  have : IsAffine (G.obj A) := A.property
  have : IsAffine (G.obj (∐ E.X)) := (∐ E.X).property
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hfppf
  have : Small.{u} E.I₀ := Countable.toSmall _
  have : ∀ i, Flat (G.map (E.f i)) := fun i => (hfppf.2 i).1
  have hmap : G.map (Sigma.desc E.f) =
      inv (sigmaComparison G E.X) ≫ Sigma.desc (fun i => G.map (E.f i)) := by
    rw [IsIso.eq_inv_comp, sigmaComparison_map_desc]
  have : Flat (G.map (Sigma.desc E.f)) := by rw [hmap]; infer_instance
  have : Surjective (G.map (Sigma.desc E.f)) := ⟨fun x => by
    obtain ⟨i, y, rfl⟩ := hfppf.1 x
    refine ⟨G.map (Sigma.ι E.X i) y, ?_⟩
    show (G.map (Sigma.ι E.X i) ≫ G.map (Sigma.desc E.f)) y = _
    rw [← G.map_comp, Sigma.ι_desc]
    rfl⟩
  have h0 : (G.map (Sigma.desc E.f)).appTop.hom.FaithfullyFlat :=
    faithfullyFlat_appTop_of_flat_of_surjective _
  let : Algebra Γ(G.obj A, ⊤) Γ(G.obj (∐ E.X), ⊤) :=
    (G.map (Sigma.desc E.f)).appTop.hom.toAlgebra
  have h0' : Module.FaithfullyFlat Γ(G.obj A, ⊤) Γ(G.obj (∐ E.X), ⊤) :=
    (RingHom.faithfullyFlat_algebraMap_iff).2 h0
  let : Algebra (ULift.{u + 1} Γ(G.obj A, ⊤)) (ULift.{u + 1} Γ(G.obj (∐ E.X), ⊤)) :=
    ULift.algebra' _ _
  have h1 : Module.FaithfullyFlat (ULift.{u + 1} Γ(G.obj A, ⊤))
      (ULift.{u + 1} Γ(G.obj (∐ E.X), ⊤)) := by
    let R := Γ(G.obj A, ⊤)
    let B := Γ(G.obj (∐ E.X), ⊤)
    have : Module.FaithfullyFlat (ULift.{u + 1} R) R :=
      Module.FaithfullyFlat.of_linearEquiv (ULift.{u + 1} R) (ULift.{u + 1} R)
        { toFun := ULift.up, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
          invFun := ULift.down, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    have : Module.FaithfullyFlat R (ULift.{u + 1} B) :=
      Module.FaithfullyFlat.of_linearEquiv R B ULift.moduleEquiv
    have : IsScalarTower (ULift.{u + 1} R) R (ULift.{u + 1} B) :=
      ⟨fun x y z => ULift.ext _ _ (mul_smul x.down y z.down)⟩
    exact Module.FaithfullyFlat.trans (ULift.{u + 1} R) R (ULift.{u + 1} B)
  have h2 := (RingHom.faithfullyFlat_algebraMap_iff).2 h1
  have h3 := RingHom.FaithfullyFlat.respectsIso.1 _
    (ringIso (∐ E.X)).commRingCatIsoToRingEquiv.symm
    (RingHom.FaithfullyFlat.respectsIso.2 _ (ringIso A).commRingCatIsoToRingEquiv h2)
  refine (RingHom.faithfullyFlat_algebraMap_iff).1 ?_
  convert h3 using 1
  case e'_5 =>
    ext a
    refine (RingEquiv.eq_symm_apply (ringIso (∐ E.X)).commRingCatIsoToRingEquiv).2 ?_
    exact congrArg (fun φ => φ.hom a) (ringIso_hom_naturality (Sigma.desc E.f))
  all_goals rfl

include hV₀ in
/-- **Stacks 03FJ on the affine schemes over an affine object `V`**: the base change presheaf
`A ↦ 𝒪(A) ⊗ M` has vanishing positive Čech cohomology on every finite family of affine schemes
over `V` whose underlying schemes form an fppf covering. -/
theorem isZero_cechCohomology_baseChangePresheaf_succ {W₀ : AffineSchemesOver T V}
    (hW₀ : IsTerminal W₀)
    (M : ModuleCat.{u + 1} ((ringPresheaf (T := T) (V := V)).obj (op W₀)))
    {A : AffineSchemesOver T V} (E : PreZeroHypercover.{u + 1} A) [Finite E.I₀]
    (hfppf : Presieve.ofArrows
        (fun i => (BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj (E.X i).obj.left)
        (fun i => (BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map (E.f i).hom.left) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj A.obj.left))
    (p : ℕ) :
    letI := hasFiniteLimits V₀ e hV₀
    IsZero (Stacks.CechSite.cechCohomology E ((Stacks.TerminalBaseChange.baseChangePresheaf.{u + 1}
      (ringPresheaf (T := T) (V := V)) hW₀).obj M).presheaf (p + 1)) := by
  let := hasFiniteLimits V₀ e hV₀
  let := finitaryExtensive V₀ e hV₀
  have := preservesFiniteProducts_baseChangePresheaf V₀ hV₀ e hW₀ M
  exact Stacks.CartesianModuleCech.isZero_cechCohomology_succ hW₀ M E
    (fun c hc => isPushout_ringPresheaf_of_isLimit V₀ e c hc)
    (faithfullyFlat_sigmaDesc V₀ hV₀ e E hfppf) p

end BigFppfSpaceSite.AffineSchemesOver

end AlgebraicGeometry

end
