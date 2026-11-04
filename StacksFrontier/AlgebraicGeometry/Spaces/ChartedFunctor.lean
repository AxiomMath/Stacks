module

public import StacksFrontier.RingTheory.ChartedFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Category

/-!
# Presheaves over an affine object as functors on algebras

Let `T'` be an object of the big fppf site of `S` with affine underlying scheme, `A' = Γ(T')`,
and let `p : X ⟶ h_{T'}` be a morphism of presheaves on the site. Every `A'`-algebra `P` of
cardinality below the cutoff of the site has a spectrum `Spec P` which is an object of the site
over `T'`, so `X` gives a functor `P ↦ {ξ ∈ X(Spec P) | p(ξ) = (Spec P ⟶ T')}` on such algebras.
This file sets up that functor and two of its properties, the hypotheses of the infinitesimal
lifting criterion for algebraic spaces ([Stacks Project, Tag 04AM]):

* an étale morphism `a : h_{U₀} ⟶ X` from an affine object `U₀` lying over a smooth morphism
  `U₀ ⟶ T'` is an étale chart of the functor: the global sections `Γ(U₀)` are a smooth
  `A'`-algebra, and the transformation `Hom_{A'}(Γ(U₀), -) ⟶ X` has unique liftings along
  surjections with square-zero kernel;
* if `X` is a sheaf, the functor satisfies descent along a faithfully flat étale map of
  algebras.

## Main definitions

* `AlgebraicGeometry.Space.OverAffine.specOver`: the spectrum of a bounded `Γ(T')`-algebra, as
  an object of the site, with `AlgebraicGeometry.Space.OverAffine.specOverToBase` and
  `AlgebraicGeometry.Space.OverAffine.specOverMap`.
* `AlgebraicGeometry.Space.OverAffine.chartedFunctor`: the functor on bounded algebras attached
  to `p`.
* `AlgebraicGeometry.Space.OverAffine.etaleChart`: the étale chart attached to an étale morphism
  from an affine object over a smooth morphism to `T'`.

## Main results

* `AlgebraicGeometry.Space.OverAffine.chartTrans_formallyEtale`: unique lifting of the chart.
* `AlgebraicGeometry.Space.OverAffine.chartedFunctor_existsUnique_of_isPushout`: descent along a
  faithfully flat étale map of algebras.
* `AlgebraicGeometry.Space.OverAffine.chartedFunctor_map_injective`: separatedness along such a
  map.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open CategoryTheory Opposite Cardinal Limits

universe u

namespace AlgebraicGeometry.Space.OverAffine


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (T' : BigFppfOver B S hS)

/-- The ring of global sections of an object of the site. -/
abbrev sectionsRing : CommRingCat.{u} := Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)

open Stacks.ChartedFunctor

/-- The spectrum of an algebra over the global sections of `T'` of cardinality below the cutoff is
contained in the site. -/
lemma contains_spec_of_boundedAlg (P : BoundedAlg (sectionsRing T') B.cutoff) :
    B.Contains (Spec (CommRingCat.of P.obj)) := by
  show (Spec (CommRingCat.of P.obj)).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff P.2

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

/-- The structure morphism `Spec P ⟶ T'` of an algebra over the global sections of `T'`. -/
noncomputable def specToBase (P : BoundedAlg (sectionsRing T') B.cutoff) :
    Spec (CommRingCat.of P.obj) ⟶ (BigFppfOver.toScheme B S hS).obj T' :=
  Spec.map (CommRingCat.ofHom (algebraMap (sectionsRing T') P.obj)) ≫
    ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv

/-- The spectrum of a bounded algebra over the global sections of `T'`, as an object of the
site. -/
noncomputable def specOver (P : BoundedAlg (sectionsRing T') B.cutoff) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_spec_of_boundedAlg T' P)
    (specToBase T' P ≫ B.inclusion.map T'.hom)

/-- The structure morphism `Spec P ⟶ T'`, as a morphism of the site. -/
noncomputable def specOverToBase (P : BoundedAlg (sectionsRing T') B.cutoff) :
    specOver T' P ⟶ T' :=
  Over.homMk (ObjectProperty.homMk (specToBase T' P)) (by
    apply ObjectProperty.hom_ext
    rfl)

/-- The underlying scheme morphism of `specOverToBase T' P` is `specToBase T' P`. -/
@[simp]
lemma toScheme_map_specOverToBase (P : BoundedAlg (sectionsRing T') B.cutoff) :
    (BigFppfOver.toScheme B S hS).map (specOverToBase T' P) = specToBase T' P := rfl

/-- For a morphism `f : P ⟶ Q` of bounded algebras, `Spec Q ⟶ Spec P ⟶ T'` is the structure
morphism `Spec Q ⟶ T'`. -/
lemma specMap_comp_specToBase {P Q : BoundedAlg (sectionsRing T') B.cutoff} (f : P ⟶ Q) :
    Spec.map (CommRingCat.ofHom (BoundedAlg.toAlgHom f).toRingHom) ≫ specToBase T' P =
      specToBase T' Q := by
  simp only [specToBase, ← Category.assoc, ← Spec.map_comp]
  congr 3
  ext a
  exact (BoundedAlg.toAlgHom f).commutes a

/-- The morphism of spectra induced by a morphism of bounded algebras. -/
noncomputable def specOverMap {P Q : BoundedAlg (sectionsRing T') B.cutoff} (f : P ⟶ Q) :
    specOver T' Q ⟶ specOver T' P :=
  BigFppfOver.homMk B S hS (contains_spec_of_boundedAlg T' P)
    (specToBase T' P ≫ B.inclusion.map T'.hom)
    (Spec.map (CommRingCat.ofHom (BoundedAlg.toAlgHom f).toRingHom)) (by
      change Spec.map (CommRingCat.ofHom (BoundedAlg.toAlgHom f).toRingHom) ≫
        specToBase T' P ≫ B.inclusion.map T'.hom = specToBase T' Q ≫ B.inclusion.map T'.hom
      rw [← Category.assoc, specMap_comp_specToBase])

/-- For a morphism `f : P ⟶ Q` of bounded algebras, `specOverMap T' f` is a morphism over `T'`. -/
@[simp]
lemma specOverMap_comp_specOverToBase {P Q : BoundedAlg (sectionsRing T') B.cutoff}
    (f : P ⟶ Q) : specOverMap T' f ≫ specOverToBase T' P = specOverToBase T' Q :=
  (BigFppfOver.toScheme B S hS).map_injective
    (((BigFppfOver.toScheme B S hS).map_comp _ _).trans (specMap_comp_specToBase T' f))

/-- `specOverMap` sends the identity of `P` to the identity of `specOver T' P`. -/
lemma specOverMap_id (P : BoundedAlg (sectionsRing T') B.cutoff) :
    specOverMap T' (𝟙 P) = 𝟙 _ := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  show Spec.map (CommRingCat.ofHom (AlgHom.id _ P.obj).toRingHom) = 𝟙 _
  exact Spec.map_id _

/-- `specOverMap` is contravariantly functorial: it sends `f ≫ g` to
`specOverMap T' g ≫ specOverMap T' f`. -/
lemma specOverMap_comp {P Q W : BoundedAlg (sectionsRing T') B.cutoff} (f : P ⟶ Q) (g : Q ⟶ W) :
    specOverMap T' (f ≫ g) = specOverMap T' g ≫ specOverMap T' f := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  show Spec.map (CommRingCat.ofHom ((BoundedAlg.toAlgHom g).comp
    (BoundedAlg.toAlgHom f)).toRingHom) = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (p : X ⟶ yoneda.obj T')

/-- **The functor on bounded algebras attached to a presheaf over `T'`**: its value at `P` is
the set of sections of `X` over `Spec P` lying over the structure morphism `Spec P ⟶ T'`. -/
noncomputable def chartedFunctor : BoundedAlg (sectionsRing T') B.cutoff ⥤ Type u where
  obj P := {ξ : X.obj (op (specOver T' P)) // p.app _ ξ = specOverToBase T' P}
  map {P Q} f := TypeCat.ofHom fun ξ => ⟨X.map (specOverMap T' f).op ξ.1, by
    rw [NatTrans.naturality_apply, ξ.2]
    exact specOverMap_comp_specOverToBase T' f⟩
  map_id P := by
    ext ξ
    change X.map (specOverMap T' (𝟙 P)).op ξ.1 = ξ.1
    rw [specOverMap_id]
    simp
  map_comp f g := by
    ext ξ
    change X.map (specOverMap T' (f ≫ g)).op ξ.1 = X.map (specOverMap T' g).op
      (X.map (specOverMap T' f).op ξ.1)
    rw [specOverMap_comp]
    simp


/-! ### The sheaf property -/

section Sheaf

variable {X}

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- The underlying ring map of a morphism of bounded algebras. -/
noncomputable abbrev ringHomOf {P Q : BoundedAlg (sectionsRing T') B.cutoff} (f : P ⟶ Q) :
    CommRingCat.of P.obj ⟶ CommRingCat.of Q.obj :=
  CommRingCat.ofHom (BoundedAlg.toAlgHom f).toRingHom

/-- The underlying scheme morphism of `specOverMap T' f` is `Spec.map (ringHomOf T' f)`. -/
lemma toScheme_map_specOverMap {P Q : BoundedAlg (sectionsRing T') B.cutoff} (f : P ⟶ Q) :
    (BigFppfOver.toScheme B S hS).map (specOverMap T' f) = Spec.map (ringHomOf T' f) := rfl

/-- A pushout square of bounded algebras gives a pullback square of their spectra in the site. -/
lemma isPullback_specOverMap {P P₁ P₂ W : BoundedAlg (sectionsRing T') B.cutoff} (f₁ : P ⟶ P₁)
    (f₂ : P ⟶ P₂) (i₁ : P₁ ⟶ W) (i₂ : P₂ ⟶ W)
    (h : IsPushout (ringHomOf T' f₁) (ringHomOf T' f₂) (ringHomOf T' i₁) (ringHomOf T' i₂)) :
    IsPullback (specOverMap T' i₁) (specOverMap T' i₂) (specOverMap T' f₁)
      (specOverMap T' f₂) := by
  refine IsPullback.of_map (BigFppfOver.toScheme B S hS) ?_ ?_
  · rw [← specOverMap_comp, ← specOverMap_comp]
    congr 1
    apply BoundedAlg.hom_ext
    ext a
    exact congrArg (fun k => k.hom a) h.w
  · exact isPullback_SpecMap_of_isPushout _ _ _ _ h

/-- A map of bounded algebras which is étale and surjective on spectra gives a covering singleton
presieve, so every sheaf is a sheaf for it. -/
private lemma isSheafFor_singleton_specOverMap {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    {P P'' : BoundedAlg (sectionsRing T') B.cutoff} (φ : P ⟶ P'')
    (het : Etale (Spec.map (ringHomOf T' φ))) (hsurj : Surjective (Spec.map (ringHomOf T' φ))) :
    Presieve.IsSheafFor Y (.singleton (specOverMap T' φ)) := by
  have hcov : Sieve.generate (Presieve.singleton (specOverMap T' φ)) ∈
      BigFppfOver.topology B S hS (specOver T' P) := by
    have := BigFppfOver.ofArrows_mem_topology_of_etale B S hS (I := PUnit.{u + 2})
      (fun _ => specOver T' P'') (fun _ => specOverMap T' φ) (fun _ => het)
      (fun y => ⟨PUnit.unit, hsurj.surj y⟩)
    rwa [Sieve.ofArrows, Presieve.ofArrows_pUnit] at this
  exact (Presieve.isSheafFor_iff_generate _).2 ((isSheaf_iff_isSheaf_of_type _ Y).1 hY _ hcov)

/-- **The functor attached to a sheaf over `T'` is a sheaf for faithfully flat étale maps.** Let
`φ : P ⟶ P''` be a map of bounded algebras which is étale and surjective on spectra, and let
`i₁, i₂ : P'' ⟶ W` present `W` as the pushout `P'' ⊗_P P''`. A section of the functor over `P''`
whose two images over `W` agree comes from a unique section over `P`. -/
theorem chartedFunctor_existsUnique_of_isPushout
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {P P'' W : BoundedAlg (sectionsRing T') B.cutoff} (φ : P ⟶ P'') (i₁ i₂ : P'' ⟶ W)
    (hpush : IsPushout (ringHomOf T' φ) (ringHomOf T' φ) (ringHomOf T' i₁) (ringHomOf T' i₂))
    (het : Etale (Spec.map (ringHomOf T' φ))) (hsurj : Surjective (Spec.map (ringHomOf T' φ)))
    (ξ : (chartedFunctor T' X p).obj P'')
    (hξ : (chartedFunctor T' X p).map i₁ ξ = (chartedFunctor T' X p).map i₂ ξ) :
    ∃! η : (chartedFunctor T' X p).obj P, (chartedFunctor T' X p).map φ η = ξ := by
  let f := specOverMap T' φ
  have hpb := isPullback_specOverMap T' φ φ i₁ i₂ hpush
  have hsheaf : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y → Presieve.IsSheafFor Y (.singleton f) :=
    fun _ hY => isSheafFor_singleton_specOverMap T' hY φ het hsurj
  have hcompat : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (y : Y.obj (op (specOver T' P''))),
      Y.map (specOverMap T' i₁).op y = Y.map (specOverMap T' i₂).op y →
      ∀ {Z : BigFppfOver B S hS} (p₁ p₂ : Z ⟶ specOver T' P''), p₁ ≫ f = p₂ ≫ f →
        Y.map p₁.op y = Y.map p₂.op y := by
    intro Y y hy Z p₁ p₂ h
    obtain ⟨l, hl₁, hl₂⟩ := hpb.exists_lift p₁ p₂ h
    rw [← hl₁, ← hl₂, op_comp, op_comp, Y.map_comp, Y.map_comp, types_comp_apply,
      types_comp_apply, hy]
  obtain ⟨η, hη, hηu⟩ := (Presieve.isSheafFor_singleton.1 (hsheaf X hX)) ξ.1
    (hcompat X ξ.1 (congrArg Subtype.val hξ))
  have hηT : p.app _ η = specOverToBase T' P := by
    have hY := (isAlgebraicSpace_yoneda B S hS T').isSheaf
    obtain ⟨t, -, htu⟩ := (Presieve.isSheafFor_singleton.1 (hsheaf _ hY))
      (specOverToBase T' P'') (hcompat _ _ (by
        show specOverMap T' i₁ ≫ specOverToBase T' P'' =
          specOverMap T' i₂ ≫ specOverToBase T' P''
        rw [specOverMap_comp_specOverToBase, specOverMap_comp_specOverToBase]))
    have e₁ : (yoneda.obj T').map f.op (p.app _ η) = specOverToBase T' P'' := by
      rw [← NatTrans.naturality_apply, hη]
      exact ξ.2
    have e₂ : (yoneda.obj T').map f.op (specOverToBase T' P) = specOverToBase T' P'' :=
      specOverMap_comp_specOverToBase T' φ
    exact (htu _ e₁).trans (htu _ e₂).symm
  exact ⟨⟨η, hηT⟩, Subtype.ext hη, fun η' h => Subtype.ext (hηu _ (congrArg Subtype.val h))⟩

/-- **The functor attached to a sheaf over `T'` is separated along maps with étale surjective
spectrum.** -/
theorem chartedFunctor_map_injective
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {P P'' : BoundedAlg (sectionsRing T') B.cutoff} (φ : P ⟶ P'')
    (het : Etale (Spec.map (ringHomOf T' φ))) (hsurj : Surjective (Spec.map (ringHomOf T' φ))) :
    Function.Injective ((chartedFunctor T' X p).map φ) := by
  intro η₁ η₂ h
  refine Subtype.ext <| (isSheafFor_singleton_specOverMap T' hX φ het hsurj).isSeparatedFor.ext
    fun Y g hg => ?_
  obtain ⟨⟩ := hg
  exact congrArg Subtype.val h

end Sheaf

/-! ### A chart -/

section Chart

variable {T'} (U₀ : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)]
  (q : U₀ ⟶ T')

/-- The algebra structure on the global sections of `U₀` over those of `T'` along `q`. -/
noncomputable abbrev chartAlgebraStruct :
    Algebra (sectionsRing T') Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤) :=
  ((BigFppfOver.toScheme B S hS).map q).appTop.hom.toAlgebra

/-- The global sections of `U₀`, as an algebra over the global sections of `T'` along `q`. -/
noncomputable def chartAlgebra : CommAlgCat.{u} (sectionsRing T') :=
  letI := chartAlgebraStruct U₀ q
  CommAlgCat.of (sectionsRing T') Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤)

/-- The underlying ring map of an algebra map out of `chartAlgebra`. -/
noncomputable abbrev chartRingHom {P : BoundedAlg (sectionsRing T') B.cutoff}
    (ρ : chartAlgebra U₀ q ⟶ P.obj) :
    Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤) ⟶ CommRingCat.of P.obj :=
  CommRingCat.ofHom ρ.hom.toRingHom

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)] in
/-- The ring map `Γ(T') ⟶ Γ(U₀) ⟶ P` through an algebra map `ρ : Γ(U₀) ⟶ P` is the structure
map of `P`. -/
lemma chartRingHom_comp_appTop {P : BoundedAlg (sectionsRing T') B.cutoff}
    (ρ : chartAlgebra U₀ q ⟶ P.obj) :
    ((BigFppfOver.toScheme B S hS).map q).appTop ≫ chartRingHom U₀ q ρ =
      CommRingCat.ofHom (algebraMap (sectionsRing T') P.obj) := by
  ext a
  exact ρ.hom.commutes a

/-- The scheme morphism `Spec P ⟶ U₀` named by an algebra map `Γ(U₀) ⟶ P`. -/
noncomputable def chartSchemeHom {P : BoundedAlg (sectionsRing T') B.cutoff}
    (ρ : chartAlgebra U₀ q ⟶ P.obj) :
    Spec (CommRingCat.of P.obj) ⟶ (BigFppfOver.toScheme B S hS).obj U₀ :=
  Spec.map (chartRingHom U₀ q ρ) ≫ ((BigFppfOver.toScheme B S hS).obj U₀).isoSpec.inv

/-- The composite `Spec P ⟶ U₀ ⟶ T'` of `chartSchemeHom U₀ q ρ` with `q` is the structure
morphism `specToBase T' P`. -/
lemma chartSchemeHom_comp {P : BoundedAlg (sectionsRing T') B.cutoff}
    (ρ : chartAlgebra U₀ q ⟶ P.obj) :
    chartSchemeHom U₀ q ρ ≫ (BigFppfOver.toScheme B S hS).map q = specToBase T' P := by
  rw [chartSchemeHom, Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc,
    ← Spec.map_comp, chartRingHom_comp_appTop]
  rfl

/-- The morphism of the site `Spec P ⟶ U₀` named by an algebra map `Γ(U₀) ⟶ P`. -/
noncomputable def chartHom {P : BoundedAlg (sectionsRing T') B.cutoff}
    (ρ : chartAlgebra U₀ q ⟶ P.obj) : specOver T' P ⟶ U₀ :=
  Over.homMk (ObjectProperty.homMk (chartSchemeHom U₀ q ρ)) (by
    apply ObjectProperty.hom_ext
    change chartSchemeHom U₀ q ρ ≫ B.inclusion.map U₀.hom =
      specToBase T' P ≫ B.inclusion.map T'.hom
    rw [← chartSchemeHom_comp U₀ q ρ, Category.assoc]
    congr 1
    change _ = B.inclusion.map (q.left ≫ T'.hom)
    rw [Over.w])

/-- The underlying scheme morphism of `chartHom U₀ q ρ` is `chartSchemeHom U₀ q ρ`. -/
@[simp]
lemma toScheme_map_chartHom {P : BoundedAlg (sectionsRing T') B.cutoff}
    (ρ : chartAlgebra U₀ q ⟶ P.obj) :
    (BigFppfOver.toScheme B S hS).map (chartHom U₀ q ρ) = chartSchemeHom U₀ q ρ := rfl

/-- The morphism `chartHom U₀ q ρ : Spec P ⟶ U₀` lies over `T'`. -/
@[simp]
lemma chartHom_comp {P : BoundedAlg (sectionsRing T') B.cutoff}
    (ρ : chartAlgebra U₀ q ⟶ P.obj) : chartHom U₀ q ρ ≫ q = specOverToBase T' P :=
  (BigFppfOver.toScheme B S hS).map_injective
    (((BigFppfOver.toScheme B S hS).map_comp _ _).trans (chartSchemeHom_comp U₀ q ρ))

/-- Precomposing `chartHom U₀ q ρ` with the morphism of spectra induced by `f : P ⟶ Q` gives
`chartHom U₀ q (ρ ≫ f.hom)`. -/
lemma specOverMap_comp_chartHom {P Q : BoundedAlg (sectionsRing T') B.cutoff} (f : P ⟶ Q)
    (ρ : chartAlgebra U₀ q ⟶ P.obj) :
    specOverMap T' f ≫ chartHom U₀ q ρ = chartHom U₀ q (ρ ≫ f.hom) := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp]
  show Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- Every morphism of the site `Spec P ⟶ U₀` over `T'` is named by an algebra map. -/
lemma exists_chartHom_eq {P : BoundedAlg (sectionsRing T') B.cutoff} (z : specOver T' P ⟶ U₀)
    (hz : z ≫ q = specOverToBase T' P) : ∃ ρ : chartAlgebra U₀ q ⟶ P.obj, chartHom U₀ q ρ = z := by
  let zS : Spec (CommRingCat.of P.obj) ⟶ (BigFppfOver.toScheme B S hS).obj U₀ :=
    (BigFppfOver.toScheme B S hS).map z
  have hzS : zS ≫ (BigFppfOver.toScheme B S hS).map q = specToBase T' P :=
    ((BigFppfOver.toScheme B S hS).map_comp z q).symm.trans
      (congrArg (BigFppfOver.toScheme B S hS).map hz)
  let g : Spec (CommRingCat.of P.obj) ⟶ Spec Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤) :=
    zS ≫ ((BigFppfOver.toScheme B S hS).obj U₀).isoSpec.hom
  let φ : Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤) ⟶ CommRingCat.of P.obj := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hcomm : ((BigFppfOver.toScheme B S hS).map q).appTop ≫ φ =
      CommRingCat.ofHom (algebraMap (sectionsRing T') P.obj) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ]
    simp only [g, Category.assoc, Scheme.isoSpec_hom_naturality]
    rw [← Category.assoc, hzS, specToBase, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let := chartAlgebraStruct U₀ q
  let ρh : Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤) →ₐ[sectionsRing T'] P.obj :=
    { toRingHom := φ.hom
      commutes' := fun a => congrArg (fun k => k.hom a) hcomm }
  let ρ : chartAlgebra U₀ q ⟶ P.obj := CommAlgCat.ofHom ρh
  refine ⟨ρ, (BigFppfOver.toScheme B S hS).map_injective ?_⟩
  show chartSchemeHom U₀ q ρ = zS
  rw [chartSchemeHom, show chartRingHom U₀ q ρ = φ from rfl, hφ]
  simp [g]

/-- Distinct algebra maps `Γ(U₀) ⟶ P` name distinct morphisms `Spec P ⟶ U₀`. -/
lemma chartHom_injective {P : BoundedAlg (sectionsRing T') B.cutoff}
    {ρ ρ' : chartAlgebra U₀ q ⟶ P.obj} (h : chartHom U₀ q ρ = chartHom U₀ q ρ') : ρ = ρ' := by
  have h1 : chartSchemeHom U₀ q ρ = chartSchemeHom U₀ q ρ' :=
    congrArg (BigFppfOver.toScheme B S hS).map h
  rw [chartSchemeHom, chartSchemeHom, cancel_mono] at h1
  ext c
  exact congrArg (fun k => k.hom c) (Spec.map_injective h1)

variable {X p}

/-- **The chart attached to a morphism from `U₀` over `T'`.** An algebra map `Γ(U₀) ⟶ P` names
a morphism `Spec P ⟶ U₀`, whose image under `a` is a section of `X` over `Spec P` lying over
`T'`. -/
noncomputable def chartTrans (a : yoneda.obj U₀ ⟶ X) (haq : a ≫ p = yoneda.map q) :
    corep (κ := B.cutoff) (chartAlgebra U₀ q) ⟶ chartedFunctor T' X p where
  app P := TypeCat.ofHom fun ρ => ⟨a.app _ (chartHom U₀ q ρ), by
    have := congrArg (fun t => t.app (op (specOver T' P)) (chartHom U₀ q ρ)) haq
    simp only [FunctorToTypes.comp] at this
    rw [this]
    exact chartHom_comp U₀ q ρ⟩
  naturality P Q f := by
    ext ρ
    apply Subtype.ext
    change a.app _ (chartHom U₀ q (ρ ≫ f.hom)) = X.map (specOverMap T' f).op
      (a.app _ (chartHom U₀ q ρ))
    rw [← NatTrans.naturality_apply, ← specOverMap_comp_chartHom]
    rfl

/-- The section of `X` named by `ρ` under `chartTrans U₀ q a haq` is the image under `a` of
`chartHom U₀ q ρ`. -/
lemma chartTrans_app_val (a : yoneda.obj U₀ ⟶ X) (haq : a ≫ p = yoneda.map q)
    {P : BoundedAlg (sectionsRing T') B.cutoff} (ρ : chartAlgebra U₀ q ⟶ P.obj) :
    ((chartTrans U₀ q a haq).app P ρ).1 = a.app _ (chartHom U₀ q ρ) := rfl

/-- The spectrum of a surjection of bounded algebras with square-zero kernel is a square-zero
closed immersion of the site. -/
lemma isSquareZeroClosedImmersion_specOverMap {Q P : BoundedAlg (sectionsRing T') B.cutoff}
    (π : Q ⟶ P) (hπ : Function.Surjective (BoundedAlg.toAlgHom π))
    (hker : RingHom.ker (BoundedAlg.toAlgHom π) ^ 2 = ⊥) :
    IsSquareZeroClosedImmersion B S hS (specOverMap T' π) :=
  Stacks.Smooth.isFirstOrderThickening_specMap
    (CommRingCat.ofHom (BoundedAlg.toAlgHom π).toRingHom) hπ hker

/-- **The chart is formally étale** along every surjection of bounded algebras with square-zero
kernel, as soon as `a` is étale. -/
theorem chartTrans_formallyEtale (a : yoneda.obj U₀ ⟶ X) (haq : a ≫ p = yoneda.map q)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    ⦃Q P : BoundedAlg (sectionsRing T') B.cutoff⦄ (π : Q ⟶ P)
    (hπ : Function.Surjective (BoundedAlg.toAlgHom π))
    (hker : RingHom.ker (BoundedAlg.toAlgHom π) ^ 2 = ⊥)
    (ρ₀ : chartAlgebra U₀ q ⟶ P.obj) (ξ : (chartedFunctor T' X p).obj Q)
    (hξ : (chartedFunctor T' X p).map π ξ = (chartTrans U₀ q a haq).app P ρ₀) :
    ∃! ρ : chartAlgebra U₀ q ⟶ Q.obj, ρ ≫ π.hom = ρ₀ ∧ (chartTrans U₀ q a haq).app Q ρ = ξ := by
  have hE := formallyEtale_of_etale B S hS a ha
  have hξ' : a.app _ (chartHom U₀ q ρ₀) = X.map (specOverMap T' π).op ξ.1 :=
    (congrArg Subtype.val hξ).symm
  have hAff : ∀ R : BoundedAlg (sectionsRing T') B.cutoff,
      IsAffine ((BigFppfOver.toScheme B S hS).obj (specOver T' R)) := fun R =>
    inferInstanceAs (IsAffine (Spec (CommRingCat.of R.obj)))
  obtain ⟨z, ⟨hz₁, hz₂⟩, hzu⟩ := hE _ _ (hAff P) (hAff Q) (specOverMap T' π)
    (isSquareZeroClosedImmersion_specOverMap π hπ hker) (chartHom U₀ q ρ₀) ξ.1 hξ'
  have hzq : z ≫ q = specOverToBase T' Q := by
    have h1 : p.app _ (a.app (op (specOver T' Q)) z) = z ≫ q :=
      congrArg (fun t => t.app (op (specOver T' Q)) z) haq
    rw [← h1, hz₂]
    exact ξ.2
  obtain ⟨ρ, hρ⟩ := exists_chartHom_eq U₀ q z hzq
  have key : ∀ ρ' : chartAlgebra U₀ q ⟶ Q.obj,
      (ρ' ≫ π.hom = ρ₀ ∧ (chartTrans U₀ q a haq).app Q ρ' = ξ) ↔ chartHom U₀ q ρ' = z := by
    refine fun ρ' => ⟨fun ⟨h₁, h₂⟩ => hzu _ ⟨?_, congrArg Subtype.val h₂⟩, fun h =>
      ⟨chartHom_injective U₀ q ?_, Subtype.ext ?_⟩⟩
    · show specOverMap T' π ≫ chartHom U₀ q ρ' = chartHom U₀ q ρ₀
      rw [specOverMap_comp_chartHom, h₁]
    · rw [← specOverMap_comp_chartHom, h]
      exact hz₁
    · exact (congrArg (fun t => a.app (op (specOver T' Q)) t) h).trans hz₂
  exact ⟨ρ, (key ρ).2 hρ, fun ρ' h => chartHom_injective U₀ q (((key ρ').1 h).trans hρ.symm)⟩

/-- The global sections of `U₀` are smooth over those of `T'` when `q` is smooth. -/
lemma smooth_chartAlgebra (hq : Smooth ((BigFppfOver.toScheme B S hS).map q)) :
    Algebra.Smooth (sectionsRing T') (chartAlgebra U₀ q) := by
  have h := (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp hq
  let := chartAlgebraStruct U₀ q
  exact (RingHom.smooth_algebraMap.mp h :)

/-- **The étale chart of the functor attached to `p`** given by an étale morphism `a` from an
affine object of the site lying over a smooth morphism to `T'`. -/
noncomputable def etaleChart (a : yoneda.obj U₀ ⟶ X) (haq : a ≫ p = yoneda.map q)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hq : Smooth ((BigFppfOver.toScheme B S hS).map q)) :
    EtaleChart (chartedFunctor T' X p) where
  C := chartAlgebra U₀ q
  smooth := smooth_chartAlgebra U₀ q hq
  α := chartTrans U₀ q a haq
  formallyEtale := chartTrans_formallyEtale U₀ q a haq ha

end Chart

end AlgebraicGeometry.Space.OverAffine

end
