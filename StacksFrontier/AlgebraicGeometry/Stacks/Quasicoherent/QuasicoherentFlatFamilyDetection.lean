module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineImageCover
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFamilyRefinement

/-!
# Maps of quasi-coherent modules are detected on a flat jointly surjective family (Stacks 0GQF)

Let `𝒳` be an algebraic stack, let `I` be a set and for `i ∈ I` let `x_i : U_i → 𝒳` be an object
of `𝒳` with `x_i` flat and `∐ x_i : ∐ U_i → 𝒳` surjective.  Let `φ : 𝓕 ⟶ 𝓖` be an arrow of
`QCoh(𝒪_𝒳)` and `φ_i` its restriction to `(U_i)_{étale}`.  **Stacks 0GQF** says that `φ` is
injective, resp. surjective, resp. an isomorphism, if and only if each `φ_i` is so.

This file proves the surjectivity and isomorphism clauses, and the "if" half of the injectivity
clause, with nothing assumed beyond the source's hypotheses.  Everything goes through the flat
objects of `𝒳` lying over affine schemes:

* `φ` is an isomorphism, resp. an epimorphism, exactly when it is bijective, resp. surjective, on
  sections at every such object (`AlgebraicGeometry.Stack.isIso_of_bijective_app_flatObject`,
  and the local surjectivity criterion), and it is a monomorphism as soon as it is injective
  there, because two maps out of a quasi-coherent module agreeing at flat objects are equal;
* such an object is covered, flatly and jointly surjectively, by objects over affine schemes
  mapping flatly to the images of affine opens of the `U_i`
  (`AlgebraicGeometry.Stack.exists_flat_refinement_smallEtaleOpen`), and along a morphism of
  objects over affine schemes `φ` is the base change of itself, so flat base change carries
  injectivity, surjectivity and bijectivity from the `φ_i` to the flat affine objects and back
  (`AlgebraicGeometry.FibredSite.injective_app_of_flat_family` and its siblings).

The surjectivity of `φ_i` is surjectivity of a map of sheaves on `(U_i)_{étale}`, i.e. local
surjectivity for the étale topology; its injectivity is injectivity on all sections; and its
being an isomorphism is being an isomorphism of presheaves.  Surjectivity and isomorphy of `φ`
are taken in `QCoh(𝒪_𝒳)`, as epimorphism and isomorphism there, and injectivity as monomorphism
there.

## Main results

* `AlgebraicGeometry.Stack.eq_of_app_flatObject_eq`: two maps out of a quasi-coherent module
  agreeing on sections at flat objects over affine schemes are equal.
* `AlgebraicGeometry.Stack.mono_of_injective_app_flatObject`: a map of quasi-coherent modules
  injective on sections at flat objects over affine schemes is a monomorphism of `QCoh(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.epi_iff_surjective_app_flatObject`: an epimorphism of `QCoh(𝒪_𝒳)` is
  exactly a map surjective on sections at flat objects over affine schemes.
* `AlgebraicGeometry.Stack.isIso_iff_restrictMapToSmallEtale`: **Stacks 0GQF**, isomorphisms.
* `AlgebraicGeometry.Stack.epi_iff_restrictMapToSmallEtale`: **Stacks 0GQF**, surjectivity.
* `AlgebraicGeometry.Stack.mono_of_restrictMapToSmallEtale`: **Stacks 0GQF**, injectivity, the
  "if" half.

## References

* [Stacks Project, Tag 0GQF](https://stacks.math.columbia.edu/tag/0GQF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

section Global

variable {B S hS 𝒳}

/-- **Two maps out of a quasi-coherent module agreeing at the flat objects over affine schemes
are equal.**  At an object over an affine scheme with a morphism to a flat object over an affine
scheme, the sections of the source are spanned by restrictions of sections at the flat object;
such objects cover every object, and the target is a sheaf. -/
theorem eq_of_app_flatObject_eq
    {H : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)} (hH : H.IsQuasicoherentOnSite)
    {P : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)} (ψ₁ ψ₂ : H ⟶ P)
    (h : ∀ w, flatObject B S hS 𝒳.val w → IsAffineOver B S hS (𝒳.val.val.p.obj w) →
      ψ₁.val.app (op w) = ψ₂.val.app (op w)) : ψ₁ = ψ₂ := by
  have hz : ∀ {x z : 𝒳.val.val.obj} {f : z ⟶ x}, affineFlatAffineFactorArrows x f →
      ψ₁.val.app (op z) = ψ₂.val.app (op z) := by
    rintro x z f ⟨⟨w, hw, hwa, ⟨g⟩⟩, hza⟩
    let := FibredSite.objModule B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids H z
    let := FibredSite.objModule B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids P z
    have := FibredSite.semilinearMap_ext_of_restriction H hH g hwa hza
      (θ₁ := ((ψ₁.val.app (op z)).hom :
        H.val.obj (op z) →ₗ[FibredSite.objRing B S hS 𝒳.val.val.p z] P.val.obj (op z)))
      (θ₂ := ((ψ₂.val.app (op z)).hom :
        H.val.obj (op z) →ₗ[FibredSite.objRing B S hS 𝒳.val.val.p z] P.val.obj (op z)))
      fun s => by
        change ψ₁.val.app (op z) (H.val.map g.op s) = ψ₂.val.app (op z) (H.val.map g.op s)
        rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, h w hw hwa]
    ext s
    exact LinearMap.congr_fun this s
  apply (SheafOfModules.toSheaf _).map_injective
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply ((SheafOfModules.toSheaf _).obj P).property.hom_ext
    ⟨_, generate_affine_flatAffineFactorSieve_mem B S hS 𝒳 V.unop⟩
  rintro ⟨W, k, hk⟩
  obtain ⟨Z, k₁, k₂, hk₂, rfl⟩ := hk
  have hZ := hz hk₂
  change _ ≫ ((SheafOfModules.toSheaf _).obj P).obj.map (k₁ ≫ k₂).op =
    _ ≫ ((SheafOfModules.toSheaf _).obj P).obj.map (k₁ ≫ k₂).op
  rw [op_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc,
    ← ((SheafOfModules.toSheaf _).map ψ₁).hom.naturality,
    ← ((SheafOfModules.toSheaf _).map ψ₂).hom.naturality]
  congr 2
  ext s
  exact congrArg (fun f => f s) hZ

variable {F G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
  𝒳.val.isFiberedInGroupoids} (φ : F ⟶ G)

/-- **A map of quasi-coherent modules injective at the flat objects over affine schemes is a
monomorphism of `QCoh(𝒪_𝒳)`.** -/
theorem mono_of_injective_app_flatObject
    (h : ∀ w, flatObject B S hS 𝒳.val w → IsAffineOver B S hS (𝒳.val.val.p.obj w) →
      Function.Injective (φ.hom.val.app (op w))) : Mono φ := by
  refine ⟨fun {H} ψ₁ ψ₂ hψ => ?_⟩
  apply ObjectProperty.hom_ext
  refine eq_of_app_flatObject_eq H.property ψ₁.hom ψ₂.hom fun w hw hwa => ?_
  ext s
  exact h w hw hwa (congrArg (fun f => f.hom.val.app (op w) s) hψ)

/-- **A map of quasi-coherent modules surjective at the flat objects over affine schemes is an
epimorphism of `QCoh(𝒪_𝒳)`.** -/
theorem epi_of_surjective_app_flatObject
    (h : ∀ w, flatObject B S hS 𝒳.val w → IsAffineOver B S hS (𝒳.val.val.p.obj w) →
      Function.Surjective (φ.hom.val.app (op w))) : Epi φ := by
  have : Epi ((ObjectProperty.ι _).map φ) :=
    Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective φ.hom
      (isLocallySurjective_of_surjective_app_flatObject φ h)
  exact (ObjectProperty.ι _).epi_of_epi_map this

/-- **An epimorphism of `QCoh(𝒪_𝒳)` is surjective at the flat objects over affine schemes.**
The inclusion of `QCoh(𝒪_𝒳)` into all modules preserves colimits, hence epimorphisms; an
epimorphism of modules is locally surjective; and at an object over an affine scheme a
section which is locally in the image is in the image, by faithfully flat descent along a
finite affine fppf refinement. -/
theorem surjective_app_flatObject_of_epi [Epi φ] {w : 𝒳.val.val.obj}
    (hwa : IsAffineOver B S hS (𝒳.val.val.p.obj w)) :
    Function.Surjective (φ.hom.val.app (op w)) := by
  have : HasColimitsOfSize.{u, u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) :=
    FibredSite.hasColimitsOfSize_quasicoherentModules' B S hS _ _
  have : PreservesColimitsOfSize.{u, u} (ObjectProperty.ι (SheafOfModules.isQuasicoherentOnSite.{
      u + 1, u, u, u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf))) :=
    FibredSite.preservesColimitsOfSize_quasicoherentInclusion' B S hS _ _
  have : HasColimitsOfSize.{0, 0} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) := hasColimitsOfSizeShrink.{0, 0, u, u} _
  have : PreservesColimitsOfSize.{0, 0} (ObjectProperty.ι (SheafOfModules.isQuasicoherentOnSite.{
      u + 1, u, u, u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf))) :=
    preservesSmallestColimits_of_preservesColimits _
  have hepi : Epi φ.hom := (ObjectProperty.ι _).map_epi φ
  have : HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
      AddCommGrpCat.{u} := FlatFppf.hasSheafify_associatedTopology_ab.{u, w, u} B S hS 𝒳
  have : (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf).WEqualsLocallyBijective
      AddCommGrpCat.{u} := FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat B S hS 𝒳
  have hls := Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi φ.hom
  intro t
  obtain ⟨n, z, ψ, haff, hmem, -, hfppf⟩ := FibredSite.exists_finite_affine_fppf_ofArrows_le B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hwa
    (Presheaf.imageSieve_mem _ ((PresheafOfModules.toPresheaf _).map φ.hom.val) t)
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hfppf
  exact FibredSite.mem_range_app_of_flat_family F.property G.property φ.hom hwa ψ haff
    (fun k => (hfppf.2 k).1) hfppf.1 fun k => hmem k

/-- **Epimorphisms of `QCoh(𝒪_𝒳)` are detected at the flat objects over affine schemes.** -/
theorem epi_iff_surjective_app_flatObject :
    Epi φ ↔ ∀ w, flatObject B S hS 𝒳.val w → IsAffineOver B S hS (𝒳.val.val.p.obj w) →
      Function.Surjective (φ.hom.val.app (op w)) :=
  ⟨fun _ _ _ hwa => surjective_app_flatObject_of_epi φ hwa, epi_of_surjective_app_flatObject φ⟩

end Global

/-- A morphism of the small étale site is étale on underlying schemes. -/
theorem etale_toScheme_map_smallEtale {U : Scheme.{u}} {hU : E.Contains U}
    {V' V : SmallEtale E U hU} (g : V' ⟶ V) : Etale ((SmallEtale.toScheme E U hU).map g) := by
  have h1 : Etale ((SmallEtale.toScheme E U hU).map g ≫ E.inclusion.map V.obj.hom) := by
    have : (SmallEtale.toScheme E U hU).map g ≫ E.inclusion.map V.obj.hom =
        E.inclusion.map V'.obj.hom := by
      change E.inclusion.map g.hom.left ≫ _ = _
      rw [← Functor.map_comp]
      exact congrArg E.inclusion.map (Over.w g.hom)
    rw [this]
    infer_instance
  exact MorphismProperty.of_postcomp @Etale (W' := @Etale) _ _ inferInstance h1

section SmallEtale

variable {B S hS 𝒳} {F G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
  𝒳.val.isFiberedInGroupoids} (φ : F ⟶ G) (x₀ : 𝒳.val.val.obj)

/-- The image in `𝒳` of a morphism of the small étale site is flat on underlying schemes. -/
theorem flat_toScheme_map_smallEtaleToStack_map {V' V : (SmallEtale E (𝒳.val.val.p.obj x₀).left.1
    (contains_base B E h S hS 𝒳.val.val.p x₀))} (g : V' ⟶ V) :
    Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map ((smallEtaleToStack B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x₀).map g))) := by
  have e := toScheme_map_smallEtaleToStack_map B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    x₀ g
  have : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map ((smallEtaleToStack B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x₀).map g)) =
      ((smallEtaleToStackSchemeIso B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x₀ V').hom ≫
        (SmallEtale.toScheme E _ _).map g) ≫
        (smallEtaleToStackSchemeIso B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x₀
          V).inv := by
    rw [← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this]
  have := etale_toScheme_map_smallEtale E g
  infer_instance

/-- **Local surjectivity of `φ|_{U_étale}` gives surjectivity at the affine objects of
`U_étale`.**  A section over an affine `V` is in the image after restriction to an étale
covering, which is refined to one by affine opens; those are flat and jointly surjective over
`V`, so faithfully flat descent applies. -/
theorem surjective_app_smallEtaleToStack_of_isLocallySurjective
    (H : Presheaf.IsLocallySurjective (SmallEtale.topology E (𝒳.val.val.p.obj x₀).left.1
        (contains_base B E h S hS 𝒳.val.val.p x₀))
      (restrictMapToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x₀
      ((PresheafOfModules.toPresheaf _).map φ.hom.val)))
    (V : (SmallEtale E (𝒳.val.val.p.obj x₀).left.1 (contains_base B E h S hS 𝒳.val.val.p x₀))) (hV
        : IsAffine ((SmallEtale.toScheme E _ _).obj V)) :
    Function.Surjective (φ.hom.val.app (op ((smallEtaleToStack B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids x₀).obj V))) := by
  intro s
  have hS' := Presheaf.imageSieve_mem (SmallEtale.topology E (𝒳.val.val.p.obj x₀).left.1
      (contains_base B E h S hS 𝒳.val.val.p x₀))
    (restrictMapToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x₀
      ((PresheafOfModules.toPresheaf _).map φ.hom.val)) (U := op V) s
  have key : ∀ t : (SmallEtale.toScheme E _ _).obj V, ∃ (Y : (SmallEtale E (𝒳.val.val.p.obj
      x₀).left.1 (contains_base B E h S hS 𝒳.val.val.p x₀))) (g : Y ⟶ V),
      Presheaf.imageSieve (restrictMapToSmallEtale B E h S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids x₀
      ((PresheafOfModules.toPresheaf _).map φ.hom.val)) s g ∧
      IsAffine ((SmallEtale.toScheme E _ _).obj Y) ∧
      t ∈ Set.range ((SmallEtale.toScheme E _ _).map g) := by
    intro t
    obtain ⟨W', g, hg, t', ht'⟩ := SmallEtale.exists_mem_arrows_mem_range E _ _ hS' t
    obtain ⟨U', hU', ht'U', -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := t') trivial
    refine ⟨SmallEtale.openSubObj E _ _ W' U', SmallEtale.openSubHom E _ _ W' U' ≫ g,
      Sieve.downward_closed _ hg _, hU', ⟨⟨t', ht'U'⟩, ht'⟩⟩
  choose Y g hg hY ht using key
  refine FibredSite.mem_range_app_of_flat_family F.property G.property φ.hom
    (isAffineOver_smallEtaleToStack B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x₀ V hV)
    (fun t => (smallEtaleToStack B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x₀).map (g t))
    (fun t => isAffineOver_smallEtaleToStack B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x₀
      (Y t) (hY t))
    (fun t => flat_toScheme_map_smallEtaleToStack_map E h x₀ (g t)) (fun u => ?_)
    (fun t => hg t)
  let eV := smallEtaleToStackSchemeIso B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x₀ V
  obtain ⟨y, hy⟩ := ht (eV.hom u)
  refine ⟨eV.hom u, (smallEtaleToStackSchemeIso B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    x₀ (Y (eV.hom u))).inv y, ?_⟩
  have e := toScheme_map_smallEtaleToStack_map B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    x₀ (g (eV.hom u))
  let eY := smallEtaleToStackSchemeIso B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x₀
    (Y (eV.hom u))
  have hinv : eY.hom (eY.inv y) = y := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  apply eV.hom.injective
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  change (SmallEtale.toScheme E _ _).map (g (eV.hom u)) (eY.hom (eY.inv y)) = _
  rwa [hinv]

/-- **Surjectivity at flat affine objects gives local surjectivity of `φ|_{U_étale}`** at a
flat object over `U`: the affine opens of an object of `U_étale` cover it, and their images in
`𝒳` are flat objects over affine schemes. -/
theorem isLocallySurjective_restrict_of_surjective_app_flatObject
    (hφ : ∀ w, flatObject B S hS 𝒳.val w → IsAffineOver B S hS (𝒳.val.val.p.obj w) →
      Function.Surjective (φ.hom.val.app (op w))) (hx : flatObject B S hS 𝒳.val x₀) :
    Presheaf.IsLocallySurjective (SmallEtale.topology E (𝒳.val.val.p.obj x₀).left.1
        (contains_base B E h S hS 𝒳.val.val.p x₀))
      (restrictMapToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x₀
        ((PresheafOfModules.toPresheaf _).map φ.hom.val)) := by
  refine ⟨fun {V} s => ?_⟩
  refine (SmallEtale.topology E (𝒳.val.val.p.obj x₀).left.1
        (contains_base B E h S hS 𝒳.val.val.p x₀)).superset_covering ?_
    (SmallEtale.mem_topology_sieve₀_affineImageCover E _ _ V)
  rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff]
  rintro Y g ⟨k⟩
  exact hφ _ (flatObject_smallEtaleToStack_obj B E h S hS x₀ hx _)
    (isAffineOver_smallEtaleToStack B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x₀ _
      (SmallEtale.isAffine_affineImageCover_X E _ _ V k)) (G.obj.val.map
        ((smallEtaleToStack B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x₀).map
          ((SmallEtale.affineImageCover E _ _ V).f k)).op s)

end SmallEtale

section Family

variable {B S hS 𝒳} {F G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
  𝒳.val.isFiberedInGroupoids} (φ : F ⟶ G)
  {I : Type*} (x : I → 𝒳.val.val.obj) (hflat : ∀ i, flatObject B S hS 𝒳.val (x i))
  (hsurj : ∀ q : AlgebraicStacks.points B S hS 𝒳, ∃ i, q ∈ Set.range
    (AlgebraicStacks.pointsMap B S hS
      (fibreObjectStackMap B S hS 𝒳 (𝒳.val.val.p.obj (x i)) (Functor.Fiber.mk rfl))))

include hflat hsurj in
/-- **Injectivity of the `φ_i` gives injectivity at the flat objects over affine schemes.** -/
theorem injective_app_flatObject_of_restrict
    (H : ∀ i V, Function.Injective ((restrictMapToSmallEtale B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (x i)
        ((PresheafOfModules.toPresheaf _).map φ.hom.val)).app V))
    {w : 𝒳.val.val.obj} (hw : flatObject B S hS 𝒳.val w)
    (hwa : IsAffineOver B S hS (𝒳.val.val.p.obj w)) :
    Function.Injective (φ.hom.val.app (op w)) := by
  obtain ⟨K, v, a, i, W, b, haff, ha, hb, hjs⟩ :=
    exists_flat_refinement_smallEtaleOpen B E h S hS 𝒳 x hflat hsurj hw
  refine FibredSite.injective_app_of_flat_family F.property φ.hom hwa a haff ha hjs
    fun k => ?_
  exact FibredSite.injective_app_of_flat F.property G.property φ.hom (b k)
    (isAffineOver_smallEtaleToStack B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (x (i k)) _
      (W k).2) (haff k) (hb k) (H (i k) (op (smallEtaleOpen B E h S hS 𝒳.val.val.p (x (i k))
        (W k).1)))

include hflat hsurj in
/-- **Surjectivity of the `φ_i` at the affine opens of the `U_i` gives surjectivity at the flat
objects over affine schemes.** -/
theorem surjective_app_flatObject_of_surjective_smallEtaleOpen
    (H : ∀ i (W : ((𝒳.val.val.p.obj (x i)).left.1).affineOpens), Function.Surjective
      (φ.hom.val.app (op ((smallEtaleToStack B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (x i)).obj (smallEtaleOpen B E h S hS 𝒳.val.val.p (x i) W.1)))))
    {w : 𝒳.val.val.obj} (hw : flatObject B S hS 𝒳.val w)
    (hwa : IsAffineOver B S hS (𝒳.val.val.p.obj w)) :
    Function.Surjective (φ.hom.val.app (op w)) := by
  obtain ⟨K, v, a, i, W, b, haff, ha, hb, hjs⟩ :=
    exists_flat_refinement_smallEtaleOpen B E h S hS 𝒳 x hflat hsurj hw
  refine FibredSite.surjective_app_of_flat_family F.property G.property φ.hom hwa a haff ha hjs
    fun k => ?_
  exact FibredSite.surjective_app_of_hom G.property φ.hom (b k)
    (isAffineOver_smallEtaleToStack B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (x (i k)) _
      (W k).2) (haff k) (H (i k) (W k))

include hflat hsurj in
/-- **Stacks 0GQF, isomorphisms.**  Let `𝒳` be an algebraic stack and `x_i : U_i → 𝒳`, `i ∈ I`,
flat objects with `∐ x_i : ∐ U_i → 𝒳` surjective.  An arrow `φ` of `QCoh(𝒪_𝒳)` is an
isomorphism if and only if each restriction `φ_i = φ|_{(U_i)_{étale}}` is. -/
@[stacks 0GQF "isomorphism"]
theorem isIso_iff_restrictMapToSmallEtale :
    IsIso φ ↔ ∀ i, IsIso (restrictMapToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (x i)
        ((PresheafOfModules.toPresheaf _).map φ.hom.val)) := by
  refine ⟨fun hiso i => ?_, fun H => ?_⟩
  · have : IsIso φ.hom := (ObjectProperty.ι _).map_isIso φ
    have : IsIso φ.hom.val := (SheafOfModules.forget _).map_isIso φ.hom
    have : IsIso ((PresheafOfModules.toPresheaf _).map φ.hom.val) := Functor.map_isIso _ _
    change IsIso (Functor.whiskerLeft _ _)
    infer_instance
  · have hbij : ∀ i V, Function.Bijective ((restrictMapToSmallEtale B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (x i)
        ((PresheafOfModules.toPresheaf _).map φ.hom.val)).app V) := fun i V =>
      (ConcreteCategory.isIso_iff_bijective _).1 (NatIso.isIso_app_of_isIso _ V)
    exact isIso_of_bijective_app_flatObject φ fun w hw hwa =>
      ⟨injective_app_flatObject_of_restrict E h φ x hflat hsurj (fun i V => (hbij i V).1) hw hwa,
        surjective_app_flatObject_of_surjective_smallEtaleOpen E h φ x hflat hsurj
          (fun i W => (hbij i _).2) hw hwa⟩

include hflat hsurj in
/-- **Stacks 0GQF, surjectivity.**  Let `𝒳` be an algebraic stack and `x_i : U_i → 𝒳`,
`i ∈ I`, flat objects with `∐ x_i : ∐ U_i → 𝒳` surjective.  An arrow `φ` of `QCoh(𝒪_𝒳)` is
surjective (an epimorphism of `QCoh(𝒪_𝒳)`) if and only if each restriction
`φ_i = φ|_{(U_i)_{étale}}` is surjective as a map of sheaves on `(U_i)_{étale}`, i.e. locally
surjective for the étale topology. -/
@[stacks 0GQF "surjectivity"]
theorem epi_iff_restrictMapToSmallEtale :
    Epi φ ↔ ∀ i, Presheaf.IsLocallySurjective (SmallEtale.topology E (𝒳.val.val.p.obj (x i)).left.1
        (contains_base B E h S hS 𝒳.val.val.p (x i)))
      (restrictMapToSmallEtale B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (x i)
        ((PresheafOfModules.toPresheaf _).map φ.hom.val)) := by
  rw [epi_iff_surjective_app_flatObject]
  exact ⟨fun hφ i => isLocallySurjective_restrict_of_surjective_app_flatObject E h φ (x i) hφ
      (hflat i),
    fun H w hw hwa => surjective_app_flatObject_of_surjective_smallEtaleOpen E h φ x hflat
      hsurj (fun i W => surjective_app_smallEtaleToStack_of_isLocallySurjective E h φ (x i) (H i)
        _ W.2) hw hwa⟩

include hflat hsurj in
/-- **Stacks 0GQF, injectivity, the "if" half.**  If each restriction
`φ_i = φ|_{(U_i)_{étale}}` is injective on all sections, then `φ` is a monomorphism of
`QCoh(𝒪_𝒳)`. -/
theorem mono_of_restrictMapToSmallEtale
    (H : ∀ i V, Function.Injective ((restrictMapToSmallEtale B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (x i)
        ((PresheafOfModules.toPresheaf _).map φ.hom.val)).app V)) : Mono φ :=
  mono_of_injective_app_flatObject φ fun _ hw hwa =>
    injective_app_flatObject_of_restrict E h φ x hflat hsurj H hw hwa

end Family

end AlgebraicGeometry.Stack

end
