module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.CartesianTransport
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesian
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentEtaleLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteFlatCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.CoveringRefinesSieve
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SiteAxioms

/-!
# The small affine étale charts of a module on the affine subcategory

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `x` an object of `𝒳` lying over
the scheme `U = p(x)`. The restriction of Stacks 06W1 evaluates a presheaf on `𝒳` along the
functor `U_{étale} ⥤ 𝒳` which sends an étale `U`-scheme `V` to an object of `𝒳` over `V`
mapping to `x`, obtained from the localization equivalence `𝒳/x ≃ (Sch/U)_{fppf}` of Stacks 06W0:
the functor `AlgebraicGeometry.Stack.etaleIndex`. When `x` lies over an affine
scheme, the functor carries affine étale `U`-schemes into the affine subcategory `𝒳_{affine}` of
Stacks 0H0A, which gives the restriction `x^*𝓕|_{U_{affine, étale}}` of a module `𝓕` on
`𝒳_{affine}` to the small affine étale site of `U` of Stacks 0H0F (2):
`AlgebraicGeometry.Stack.affineChartModule`.

The base change comparisons of a module are compared with those of its restrictions, and an
arrow of `𝒳` lying over an étale morphism is isomorphic, as an arrow, to one in the image of the
index functor.

## Main definitions

* `AlgebraicGeometry.Stack.etaleIndex`: the index functor `U_{étale} ⥤ 𝒳` of Stacks 06W1 at `x`.
* `AlgebraicGeometry.Stack.affineChart`: its restriction `U_{affine, étale} ⥤ 𝒳_{affine}`, for
  `x` affine.
* `AlgebraicGeometry.Stack.affineChartModule`: **the restriction `x^*𝓕|_{U_{affine, étale}}`** of
  a module over the structure sheaf `𝒪` of `𝒳_{affine}`, a module over the structure sheaf of
  `U_{affine, étale}`.

## Main results

* `AlgebraicGeometry.Stack.isAffine_etaleIndex_obj` and
  `AlgebraicGeometry.Stack.etale_etaleIndex_map`: the index functor carries affine étale
  `U`-schemes to affine objects and morphisms of the small étale site to arrows lying over étale
  morphisms.
* `AlgebraicGeometry.Stack.bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff` and
  `AlgebraicGeometry.Stack.bijective_restrictionBaseChange_affineChartModule_iff`: the restriction
  of Stacks 06WJ, and its affine counterpart, is cartesian over a morphism exactly when the module
  is cartesian over its image.
* `AlgebraicGeometry.Stack.exists_arrowIso_etaleIndex`: an arrow `x ⟶ x'` lying over an étale
  morphism is isomorphic, as an arrow of `𝒳`, to the image under the index functor at `x'` of the
  arrow from its chart to the final object.
* `AlgebraicGeometry.Stack.AffineCategory.exists_etale_refinement`: a covering sieve of the
  associated affine étale site contains a finite family lying over an étale covering.

## References

* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0H0A](https://stacks.math.columbia.edu/tag/0H0A)
* [Stacks Project, Tag 0H0F](https://stacks.math.columbia.edu/tag/0H0F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.PresheafOfModules

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-! ### The index functor of Stacks 06W1 -/

/-- **The index functor of Stacks 06W1 at `x`.** An étale scheme `V` over the scheme `U` below `x`
is sent to the object of `𝒳` over `V` mapping to `x` that the localization equivalence
`𝒳/x ≃ (Sch/U)_{fppf}` of Stacks 06W0 attaches to it. -/
noncomputable abbrev etaleIndex (x : 𝒳) :
    SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x) ⥤ 𝒳 :=
  letI := isEquivalence_overPost B S hS p hp x
  smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x

/-- The counit of the localization equivalence identifies the scheme below the image of `T` under
the index functor with the scheme underlying `T`. -/
noncomputable def etaleIndexIso (x : 𝒳)
    (T : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :
    (BigFppfOver.toScheme B S hS).obj (p.obj ((etaleIndex B E h S hS p hp x).obj T)) ≅
      (SmallEtale.toScheme E _ _).obj T :=
  letI := isEquivalence_overPost B S hS p hp x
  B.inclusion.mapIso ((Over.forget _).mapIso
    ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counitIso.app
      ((smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)).obj T)))

/-- The identification `AlgebraicGeometry.Stack.etaleIndexIso` is natural. -/
@[reassoc]
theorem etaleIndexIso_naturality (x : 𝒳)
    {T T' : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)} (g : T ⟶ T') :
    (BigFppfOver.toScheme B S hS).map (p.map ((etaleIndex B E h S hS p hp x).map g)) ≫
        (etaleIndexIso B E h S hS p hp x T').hom =
      (etaleIndexIso B E h S hS p hp x T).hom ≫ (SmallEtale.toScheme E _ _).map g := by
  let := isEquivalence_overPost B S hS p hp x
  have := (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counitIso.hom.naturality
    ((smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)).map g)
  have h2 := congrArg (fun k ↦ B.inclusion.map k.left) this
  simp only [Functor.comp_map, Functor.map_comp, Over.comp_left] at h2
  exact h2

/-- The index functor sends an object of the small étale site with affine underlying scheme to an
object of `𝒳` lying over an affine scheme. -/
theorem isAffine_etaleIndex_obj (x : 𝒳)
    (T : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x))
    (hT : IsAffine ((SmallEtale.toScheme E _ _).obj T)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj ((etaleIndex B E h S hS p hp x).obj T))) :=
  IsAffine.of_isIso (etaleIndexIso B E h S hS p hp x T).hom

/-- The index functor sends a morphism of the small étale site to an arrow of `𝒳` lying over an
étale morphism of schemes. -/
theorem etale_etaleIndex_map (x : 𝒳)
    {T T' : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)} (g : T ⟶ T') :
    Etale ((BigFppfOver.toScheme B S hS).map (p.map ((etaleIndex B E h S hS p hp x).map g))) := by
  have hg := SmallEtale.etale_toScheme_map g
  have hcomp : (BigFppfOver.toScheme B S hS).map (p.map ((etaleIndex B E h S hS p hp x).map g)) =
      (etaleIndexIso B E h S hS p hp x T).hom ≫ (SmallEtale.toScheme E _ _).map g ≫
        (etaleIndexIso B E h S hS p hp x T').inv := by
    rw [← Category.assoc, ← etaleIndexIso_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [hcomp]
  infer_instance

/-- **The restriction of Stacks 06WJ is cartesian over a morphism `g` of the small étale site
exactly when the module is cartesian over the image of `g` under the index functor.** -/
theorem bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff
    (G : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (x : 𝒳) {T T' : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (g : T ⟶ T') :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u}
        (R := SmallEtale.commStructurePresheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
        (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B) G) g.op) ↔
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        G ((etaleIndex B E h S hS p hp x).map g).op) :=
  Stacks.PresheafOfModules.bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff
    (etaleIndex B E h S hS p hp x)
    (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj
    (SmallEtale.commStructurePresheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
    (localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B)).hom
    (fun Z => ((localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B)).app Z).isIso_hom) G g.op

/-! ### Charts of an arrow lying over an étale morphism -/

/-- The final object of the small étale site of the scheme below `x`. -/
noncomputable abbrev etaleTop (x : 𝒳) :
    SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x) :=
  ⟨Over.mk (𝟙 (E.obj (p.obj x).left.1 (contains_base B E h S hS p x))),
    show Etale (E.inclusion.map (𝟙 (E.obj (p.obj x).left.1 (contains_base B E h S hS p x)))) by
      change Etale (𝟙 _); infer_instance⟩

/-- The arrow of the small étale site of the scheme below `x'` from the chart of an arrow
`f : x ⟶ x'` lying over an étale morphism to the final object. -/
noncomputable abbrev etaleChartToTop {x x' : 𝒳} (f : x ⟶ x')
    (hf : Etale (B.inclusion.map (p.map f).left)) :
    etaleChart B E h S hS p f hf ⟶ etaleTop B E h S hS p x' :=
  ObjectProperty.homMk (Over.homMk (smallEtaleBaseMorphism B E h S hS p f) (Category.comp_id _))

/-- **An arrow lying over an étale morphism is, up to isomorphism, in the image of the index
functor.** For `f : x ⟶ x'` lying over an étale morphism, `f` is isomorphic as an arrow of `𝒳`
to the image under the index functor at `x'` of the arrow from the chart of `f` to the final
object. -/
theorem exists_arrowIso_etaleIndex {x x' : 𝒳} (f : x ⟶ x')
    (hf : Etale (B.inclusion.map (p.map f).left)) :
    ∃ (e₁ : x ≅ (etaleIndex B E h S hS p hp x').obj (etaleChart B E h S hS p f hf))
      (e₂ : x' ≅ (etaleIndex B E h S hS p hp x').obj (etaleTop B E h S hS p x')),
      f ≫ e₂.hom = e₁.hom ≫ (etaleIndex B E h S hS p hp x').map
        (etaleChartToTop B E h S hS p f hf) := by
  let := isEquivalence_overPost B S hS p hp x'
  let P := Over.post (X := x') (p ⋙ Over.forget (B.obj hS))
  let i := smallEtaleInclusion B E h (p.obj x').left.1 (contains_base B E h S hS p x')
  let c₁ : P.obj (Over.mk f) ≅ i.obj (etaleChart B E h S hS p f hf) := Iso.refl _
  let e₁ : Over.mk f ≅ P.inv.obj (i.obj (etaleChart B E h S hS p f hf)) :=
    P.asEquivalence.unitIso.app (Over.mk f) ≪≫ P.inv.mapIso c₁
  have hT₀ : IsTerminal (i.obj (etaleTop B E h S hS p x')) := Over.mkIdTerminal
  have hT : IsTerminal (P.inv.obj (i.obj (etaleTop B E h S hS p x'))) := hT₀.isTerminalObj P.inv
  let e₂ : Over.mk (𝟙 x') ≅ P.inv.obj (i.obj (etaleTop B E h S hS p x')) :=
    Over.mkIdTerminal.uniqueUpToIso hT
  refine ⟨(Over.forget x').mapIso e₁, (Over.forget x').mapIso e₂, ?_⟩
  have hsq : Over.homMk f (by simp) ≫ e₂.hom =
      e₁.hom ≫ P.inv.map (i.map (etaleChartToTop B E h S hS p f hf)) := hT.hom_ext _ _
  exact congrArg CommaMorphism.left hsq

/-! ### The small affine étale charts of a module on the affine subcategory -/

/-- **The affine chart functor at an object `x` of `𝒳_{affine}`**: the index functor of Stacks
06W1, restricted to the small affine étale site of the scheme `U` below `x`, lands in the affine
subcategory. -/
noncomputable def affineChart (x : AffineCategory B S hS p) :
    SmallAffineEtale E (p.obj x.obj).left.1 (contains_base B E h S hS p x.obj) ⥤
      AffineCategory B S hS p :=
  ObjectProperty.lift _
    (SmallAffineEtale.inclusion E _ _ ⋙ etaleIndex B E h S hS p hp x.obj)
    (fun T ↦ isAffine_etaleIndex_obj B E h S hS p hp x.obj T.obj T.property)

/-- **The restriction `x^*𝓕|_{U_{affine, étale}}` of Stacks 0H0F (2).** For a module `𝓕` over the
structure sheaf `𝒪` of the affine subcategory and an object `x` of it lying over the affine
scheme `U`: restrict `𝓕` along the affine chart functor, and move the scalars to the structure
sheaf of `U_{affine, étale}` along the identification of structure sheaves of Stacks 06W9. -/
noncomputable def affineChartModule (x : AffineCategory B S hS p)
    (F : PresheafOfModules.{u} (affineStructurePresheaf B S hS p)) :
    PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineEtaleRingedSite E (p.obj x.obj).left.1
        (contains_base B E h S hS p x.obj)).O).val :=
  (PresheafOfModules.restrictScalars (Functor.whiskerLeft (SmallAffineEtale.inclusion E _ _).op
    (localStructurePresheafIso B E h S hS p hp x.obj (etaleTopology B)
      (etaleTopology_le_topology B)).hom)).obj
    ((PresheafOfModules.pushforward₀ (affineChart B E h S hS p hp x) _).obj F)

/-- **The chart `x^*𝓕|_{U_{affine, étale}}` is cartesian over a morphism `a` exactly when `𝓕` is
cartesian over the image of `a` under the affine chart functor.** -/
theorem bijective_restrictionBaseChange_affineChartModule_iff (x : AffineCategory B S hS p)
    (F : PresheafOfModules.{u} (affineStructurePresheaf B S hS p))
    {V V' : SmallAffineEtale E (p.obj x.obj).left.1 (contains_base B E h S hS p x.obj)}
    (a : V ⟶ V') :
    Function.Bijective (restrictionBaseChange.{u + 1, u, u, u}
        (R := SmallEtale.affineChartRings E _ _) (affineChartModule B E h S hS p hp x F) a.op) ↔
      Function.Bijective (restrictionBaseChange.{v, w, u, u}
        (R := affineStructureCommPresheaf B S hS p) F ((affineChart B E h S hS p hp x).map a).op) :=
  bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff
    (affineChart B E h S hS p hp x) (affineStructureCommPresheaf B S hS p)
    (SmallEtale.affineChartRings E _ _)
    (Functor.whiskerLeft (SmallAffineEtale.inclusion E _ _).op
      (localStructurePresheafIso B E h S hS p hp x.obj (etaleTopology B)
        (etaleTopology_le_topology B)).hom)
    (fun _ ↦ ((localStructurePresheafIso B E h S hS p hp x.obj (etaleTopology B)
      (etaleTopology_le_topology B)).app _).isIso_hom) F a.op

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.AffineCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **A covering sieve of the associated affine étale site contains a finite family lying over an
étale covering.** -/
theorem exists_etale_refinement (hp : p.IsFiberedInGroupoids) {U : AffineCategory B S hS p}
    (T : Sieve U)
    (hT : T ∈ associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS) U) :
    ∃ E : PreZeroHypercover.{u + 1} U, Finite E.I₀ ∧
      (E.map (toScheme B S hS p)).presieve₀ ∈
        Scheme.precoverage @Etale ((toScheme B S hS p).obj U) ∧ E.sieve₀ ≤ T := by
  classical
  have hq := isFiberedInGroupoids_toAffine B S hS p hp
  have h1 := (Functor.mem_inheritedTopology_iff_functorPushforward (toAffine B S hS p)
    (BigAffineEtale.topology B.toBigEtaleSite S hS) hq T).1 hT
  obtain ⟨D, hD, hDle⟩ := exists_covering_refining_sieve
    (BigAffineEtale.IsCovering B.toBigEtaleSite S hS)
    (BigAffineEtale.precoverage B.toBigEtaleSite S hS)
    (fun {_ _} hR ↦ by obtain ⟨E, rfl, hE⟩ := hR; exact ⟨E, hE, rfl⟩)
    (BigAffineEtale.isSite B.toBigEtaleSite S hS) h1
  have hmem : (D.map (BigAffineFppf.toScheme B S hS)).presieve₀ ∈
      Scheme.precoverage @Etale ((BigAffineFppf.toScheme B S hS).obj ((toAffine B S hS p).obj U)) :=
    hD.1.etale
  replace hmem := (Scheme.presieve₀_mem_precoverage_iff _).mp hmem
  have hfin : Finite D.I₀ := hD.2.2.1
  let Tf : BigAffineFppf B S hS ⥤ Scheme.{u} := BigAffineFppf.toScheme B S hS
  let X' : D.I₀ → BigAffineFppf B S hS := D.X
  let Df : ∀ i, X' i ⟶ (toAffine B S hS p).obj U := D.f
  have hmet : ∀ i, Etale (Tf.map (Df i)) := hmem.2
  have hmsurj : ∀ x, ∃ i, x ∈ Set.range (Tf.map (Df i)) := hmem.1
  have hfac : ∀ i, ∃ (Z : AffineCategory B S hS p) (g : Z ⟶ U)
      (k : X' i ⟶ (toAffine B S hS p).obj Z), T g ∧ k ≫ (toAffine B S hS p).map g = Df i :=
    fun i ↦ by
      obtain ⟨Z, g, k, hg, hk⟩ := hDle _ _ (Presieve.ofArrows.mk i)
      exact ⟨Z, g, k, hg, hk.symm⟩
  choose Z g k hg hk using hfac
  have hlift : ∀ i, ∃ (z : AffineCategory B S hS p) (φ : z ⟶ Z i),
      (toAffine B S hS p).IsHomLift (k i) φ := fun i ↦ hq.exists_lift (k i) (Z i) rfl
  choose z φ hφ using hlift
  have hdom : ∀ i, (toAffine B S hS p).obj (z i) = X' i := fun i ↦ by
    have := hφ i
    exact IsHomLift.domain_eq _ (k i) (φ i)
  have h2 : ∀ i, (toAffine B S hS p).map (φ i) = eqToHom (hdom i) ≫ k i := fun i ↦ by
    have := hφ i
    rw [IsHomLift.fac' (toAffine B S hS p) (k i) (φ i)]
    simp
  have e1 : ∀ i, (toAffine B S hS p).map (φ i ≫ g i) = eqToHom (hdom i) ≫ Df i := fun i ↦ by
    rw [Functor.map_comp, h2, Category.assoc, hk i]
  have hL : ∀ i, (toScheme B S hS p).map (φ i ≫ g i) =
      eqToHom (congrArg Tf.obj (hdom i)) ≫ Tf.map (Df i) := by
    intro i
    have h3 : Tf.map ((toAffine B S hS p).map (φ i ≫ g i)) = Tf.map (eqToHom (hdom i) ≫ Df i) :=
      congrArg Tf.map (e1 i)
    rw [Tf.map_comp, eqToHom_map] at h3
    exact h3
  refine ⟨⟨D.I₀, z, fun i ↦ φ i ≫ g i⟩, hfin, ?_, ?_⟩
  · refine (Scheme.presieve₀_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, fun i ↦ ?_⟩
    · obtain ⟨i, y, hy⟩ := hmsurj x
      refine ⟨i, ?_⟩
      show x ∈ Set.range ((toScheme B S hS p).map (φ i ≫ g i))
      rw [hL i]
      refine ⟨(eqToHom (congrArg Tf.obj (hdom i)).symm) y, ?_⟩
      rwa [← Scheme.Hom.comp_apply, ← Category.assoc, eqToHom_trans, eqToHom_refl,
        Category.id_comp]
    · show Etale ((toScheme B S hS p).map (φ i ≫ g i))
      rw [hL i]
      have := hmet i
      infer_instance
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact T.downward_closed (hg i) (φ i)

end AlgebraicGeometry.Stack.AffineCategory

end
