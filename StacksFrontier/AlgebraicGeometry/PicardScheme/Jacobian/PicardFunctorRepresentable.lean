module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardOfCurve
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# The Picard functor of a smooth projective curve over a separably closed field is representable

Let `k` be separably closed and `X` a smooth projective curve over `k`, with a rational point `σ`.
By [Stacks, Tag 0B9N] the map `Pic(X_T) ⟶ Pic_{X/k}(T)` is surjective with kernel the classes
pulled back from `T`, which the section splits off; so the rigidified classes, the kernel of
`σ_T^*`, map bijectively onto `Pic_{X/k}(T)`, naturally in `T`. A group scheme `P` representing
the rigidified functor `Pic_{X/k,σ}` therefore represents `Pic_{X/k}` on the big fppf site, once
it lies in the site, which it does as a countable union of opens of finite type over `k`.

## Main results

* `Stacks.RigidifiedPicard.picardFunctorRepresentableBy` — `P` represents `Pic_{X/k}`.
* `Stacks.RigidifiedPicard.isRepresentable_picardFunctor_of_isSepClosed` — **[Stacks, Tag 0B9Z]**.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RigidifiedPicard

variable (B : BigFppfSite.{u}) {k : Type u} [Field k] {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)

/-- An `S`-scheme of the site, as a scheme over `S`. -/
abbrev siteOver (T : BigFppfOver B (Spec (.of k)) hk) : Over (Spec (.of k)) :=
  Over.mk (B.inclusion.map T.hom)

/-- A morphism of `S`-schemes of the site, as a morphism of schemes over `S`. -/
abbrev siteHom {T U : BigFppfOver B (Spec (.of k)) hk} (g : T ⟶ U) :
    siteOver B hk T ⟶ siteOver B hk U :=
  Over.homMk (B.inclusion.map g.left) (by
    change B.inclusion.map g.left ≫ B.inclusion.map U.hom = B.inclusion.map T.hom
    rw [← Functor.map_comp, Over.w g])

variable [Flat (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)]
  [IsProper (B.inclusion.map f)] [SmoothOfRelativeDimension 1 (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f)] (σ : Spec (.of k) ⟶ X)
  (hσ : σ ≫ B.inclusion.map f = 𝟙 _)

/-- The class in `Pic_{X/k}(T)` of an element of `Pic_{X/k,σ}(T)`. -/
def toSite (T : BigFppfOver B (Spec (.of k)) hk)
    (x : (functor (B.inclusion.map f) σ hσ ⋙ forget GrpCat).obj (op (siteOver B hk T))) :
    (Stacks.PicardFunctor.picardFunctor B hX hk f).obj (op T) :=
  Stacks.PicardFunctor.toPicardFunctorHom B hX hk f T
    (smallEquiv _ ((Multiplicative.toAdd x : group (B.inclusion.map f) σ hσ (siteOver B hk T)) :
      Stacks.Picard.smallOfScheme (bc (B.inclusion.map f) (siteOver B hk T))))

omit [SmoothOfRelativeDimension 1 (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)] in
/-- `toSite` is natural in `T`: it commutes with pullback along a morphism `g : T ⟶ U` of the
site. -/
theorem toSite_naturality {T U : BigFppfOver B (Spec (.of k)) hk} (g : T ⟶ U)
    (x : (functor (B.inclusion.map f) σ hσ ⋙ forget GrpCat).obj (op (siteOver B hk U))) :
    toSite B hX hk f σ hσ T
        ((functor (B.inclusion.map f) σ hσ ⋙ forget GrpCat).map (siteHom B hk g).op x) =
      (Stacks.PicardFunctor.picardFunctor B hX hk f).map g.op (toSite B hX hk f σ hσ U x) :=
  (congrArg (Stacks.PicardFunctor.toPicardFunctorHom B hX hk f T)
    (functor_map_val (B.inclusion.map f) σ hσ (siteHom B hk g) x)).trans
    (Stacks.PicardFunctor.toPicardFunctor_app_naturality B hX hk f g _)

/-- If `𝒪_U ⟶ f_{U,*}𝒪_{X_U}` is an isomorphism for every `U`, then `toSite` is a bijection from
`Pic_{X/k,σ}(T)` onto `Pic_{X/k}(T)`. -/
theorem toSite_bijective
    (hOiso : ∀ U : BigFppfOver B (Spec (.of k)) hk,
      IsIso (Stacks.PicardFunctor.baseChangeProj B hX hk f U).toLRSHom.toHom.c)
    (T : BigFppfOver B (Spec (.of k)) hk) :
    Function.Bijective (toSite B hX hk f σ hσ T) := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have mem := fun w : (functor (B.inclusion.map f) σ hσ ⋙ forget GrpCat).obj
        (op (siteOver B hk T)) =>
      (mem_group_iff (B.inclusion.map f) σ hσ _ _).1
        (Multiplicative.toAdd w : group (B.inclusion.map f) σ hσ (siteOver B hk T)).2
    exact ext_functor (B.inclusion.map f) σ hσ
      (Stacks.PicardFunctor.eq_of_schemePullbackClass_baseChangeSection_eq_zero B hX hk f
        σ hσ hOiso T _ _ (mem x) (mem y) hxy)
  · obtain ⟨c, hc⟩ := Stacks.PicardFunctor.surjective_toPicardFunctorHom B hX hk f σ hσ hOiso T z
    have hn := schemePullbackClass_bcSection_normalize (B.inclusion.map f) σ hσ (siteOver B hk T) c
    refine ⟨Multiplicative.ofAdd (mkGroup (B.inclusion.map f) σ hσ _ hn), ?_⟩
    have h1 := smallEquiv_mkGroup (B.inclusion.map f) σ hσ _ hn
    refine (congrArg (Stacks.PicardFunctor.toPicardFunctorHom B hX hk f T) h1).trans ?_
    rw [normalize, map_sub, hc]
    have h0 := Stacks.PicardFunctor.toPicardFunctorHom_schemePullbackClass_baseChangeProj B hX hk f
      T (Stacks.Picard.schemePullbackClass (bcSection (B.inclusion.map f) σ hσ (siteOver B hk T)) c)
    exact (congrArg (fun w => z - w) h0).trans (sub_zero z)

section Representable

variable (P : Grp (Over (Spec (.of k)))) (e : yonedaGrp.obj P ≅ functor (B.inclusion.map f) σ hσ)
  (hP : B.Contains P.X.left)

/-- The object of the site underlying a group scheme `P` over `k` contained in the site. -/
abbrev siteObj : BigFppfOver B (Spec (.of k)) hk :=
  Over.mk (B.inclusion.preimage P.X.hom : B.obj hP ⟶ B.obj hk)

/-- The structure morphism of `siteObj P` is that of `P`. -/
theorem siteObj_hom : B.inclusion.map (siteObj B hk P hP).hom = P.X.hom :=
  Functor.map_preimage _ _

/-- A morphism `a : T ⟶ siteObj P` of the site is, as a morphism of schemes, a morphism over
`k`. -/
theorem toOverHom_w {T : BigFppfOver B (Spec (.of k)) hk} (a : T ⟶ siteObj B hk P hP) :
    B.inclusion.map a.left ≫ P.X.hom = (siteOver B hk T).hom := by
  rw [← siteObj_hom B hk P hP, ← Functor.map_comp, Over.w a]
  rfl

/-- A morphism of the site to `siteObj P`, as a morphism of schemes over `k` to `P`. -/
def toOverHom {T : BigFppfOver B (Spec (.of k)) hk} (a : T ⟶ siteObj B hk P hP) :
    siteOver B hk T ⟶ P.X :=
  Over.homMk (B.inclusion.map a.left) (toOverHom_w B hk P hP a)

/-- The underlying morphism of schemes of `toOverHom a` is that of `a`. -/
theorem toOverHom_left {T : BigFppfOver B (Spec (.of k)) hk} (a : T ⟶ siteObj B hk P hP) :
    (toOverHom B hk P hP a).left = B.inclusion.map a.left := rfl

/-- `toOverHom` is a bijection from morphisms `T ⟶ siteObj P` of the site to morphisms of schemes
over `k` from `T` to `P`. -/
theorem toOverHom_bijective (T : BigFppfOver B (Spec (.of k)) hk) :
    Function.Bijective (toOverHom B hk P hP (T := T)) := by
  refine ⟨fun a a' h => ?_, fun b => ?_⟩
  · apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    rw [← toOverHom_left, ← toOverHom_left, h]
  · have hw : B.inclusion.preimage (X := T.left) (Y := B.obj hP) b.left ≫
        (siteObj B hk P hP).hom = T.hom := by
      apply B.inclusion.map_injective
      rw [Functor.map_comp, Functor.map_preimage, siteObj_hom]
      exact Over.w b
    refine ⟨Over.homMk (B.inclusion.preimage (X := T.left) (Y := B.obj hP) b.left) hw, ?_⟩
    apply Over.OverMorphism.ext
    rw [toOverHom_left]
    exact Functor.map_preimage _ _

/-- `toOverHom` is compatible with precomposition by a morphism `g : T ⟶ U` of the site. -/
theorem toOverHom_comp {T U : BigFppfOver B (Spec (.of k)) hk} (g : T ⟶ U)
    (a : U ⟶ siteObj B hk P hP) :
    toOverHom B hk P hP (g ≫ a) = siteHom B hk g ≫ toOverHom B hk P hP a := by
  apply Over.OverMorphism.ext
  rw [toOverHom_left, Over.comp_left, Over.comp_left, Functor.map_comp]
  rfl

/-- **`Pic_{X/k}` is represented by any group scheme representing `Pic_{X/k,σ}`**, when
`𝒪_T ⟶ f_{T,*}𝒪_{X_T}` is an isomorphism for every `T` ([Stacks, Tag 0B9N]). -/
def picardFunctorRepresentableBy
    (hOiso : ∀ U : BigFppfOver B (Spec (.of k)) hk,
      IsIso (Stacks.PicardFunctor.baseChangeProj B hX hk f U).toLRSHom.toHom.c) :
    (Stacks.PicardFunctor.picardFunctor B hX hk f).RepresentableBy (siteObj B hk P hP) where
  homEquiv {T} := Equiv.ofBijective
    (fun a => toSite B hX hk f σ hσ T ((e.hom.app (op (siteOver B hk T))).hom
      (toOverHom B hk P hP a)))
    ((toSite_bijective B hX hk f σ hσ hOiso T).comp
      ((((forget GrpCat).mapIso (e.app (op (siteOver B hk T)))).toEquiv.bijective).comp
        (toOverHom_bijective B hk P hP T)))
  homEquiv_comp {T U} g a := by
    change toSite B hX hk f σ hσ T ((e.hom.app (op (siteOver B hk T))).hom
      (toOverHom B hk P hP (g ≫ a))) = _
    rw [toOverHom_comp]
    have hn : (e.hom.app (op (siteOver B hk T))).hom (siteHom B hk g ≫ toOverHom B hk P hP a) =
        (functor (B.inclusion.map f) σ hσ).map (siteHom B hk g).op
          ((e.hom.app (op (siteOver B hk U))).hom (toOverHom B hk P hP a)) :=
      congrArg (fun φ => GrpCat.Hom.hom φ (toOverHom B hk P hP a))
        (e.hom.naturality (siteHom B hk g).op)
    rw [hn]
    exact toSite_naturality B hX hk f σ hσ g _

end Representable

omit [Flat (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)]
  [IsProper (B.inclusion.map f)] [SmoothOfRelativeDimension 1 (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f)] in
/-- **A Picard scheme of a curve over a field lies in the site** as soon as its degree components
are quasi-compact and locally of finite type over `k`: it is the union of countably many opens,
each of size at most that of `Spec k`. -/
theorem contains_of_degreeLocus {k : Type u} [Field k] {X : Scheme.{u}} (F : X ⟶ Spec (.of k))
    [Flat F] [LocallyOfFinitePresentation F] [IsProper F] [LocallyOfFiniteType F]
    (hdim : ∀ s, topologicalKrullDim ↥(F.fiber s) ≤ 1) (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ F = 𝟙 _)
    (P : Grp (Over (Spec (.of k)))) (e : yonedaGrp.obj P ≅ functor F σ hσ)
    (hk : B.Contains (Spec (.of k)))
    (hqc : ∀ d, QuasiCompact ((degreeLocus F hdim σ hσ P e d).ι ≫ P.X.hom))
    (hlft : ∀ d, LocallyOfFiniteType ((degreeLocus F hdim σ hσ P e d).ι ≫ P.X.hom)) :
    B.Contains P.X.left := by
  refine B.contains_of_openCover_of_size_le (ι := ULift.{u} ℤ)
    (max_lt B.aleph0_lt_cutoff hk) ?_
    (fun d => (degreeLocus F hdim σ hσ P e d.down).ι) (fun y => ?_) (fun d => ?_)
  · rw [Cardinal.mk_uLift, Cardinal.mk_int, Cardinal.lift_aleph0]
    exact le_max_left _ _
  · refine ⟨⟨degreeFunction F hdim σ hσ P e y⟩, ?_⟩
    rw [Scheme.Opens.range_ι]
    exact rfl
  · have := hqc d.down
    have := hlft d.down
    exact (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact
      ((degreeLocus F hdim σ hσ P e d.down).ι ≫ P.X.hom)).trans (le_max_right _ _)

end Stacks.RigidifiedPicard

namespace Stacks.RigidifiedPicard

/-- **[Stacks, Tag 0B9Z].** Let `k` be a separably closed field and `X` a smooth projective curve
over `k`. The Picard functor `Pic_{X/k}` is representable. -/
@[stacks 0B9Z]
theorem isRepresentable_picardFunctor_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k]
    (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) (hk : B.Contains (Spec (.of k)))
    (f : B.obj hX ⟶ B.obj hk) [IsCurve k (B.inclusion.map f)] [Smooth (B.inclusion.map f)]
    (hproj : IsProjectiveMorphism (B.inclusion.map f)) :
    (Stacks.PicardFunctor.picardFunctor B hX hk f).IsRepresentable := by
  have : IsProper (B.inclusion.map f) := isProper_of_isProjectiveMorphism _ hproj
  have : GeometricallyIrreducible (B.inclusion.map f) :=
    geometricallyIrreducible_of_isCurve_of_isSepClosed k _
  have : SmoothOfRelativeDimension 1 (B.inclusion.map f) :=
    smoothOfRelativeDimension_one_of_isCurve k _
  have : IsIntegral X := isIntegral_of_smooth_geometricallyIrreducible (B.inclusion.map f)
  obtain ⟨σ, hσ, P, e, -, -, h1, -⟩ := exists_picardScheme_of_claim k (B.inclusion.map f) hproj
    (Stacks.WeilCohomology.cohomologyLocusDivisorExistence k)
    (Stacks.WeilCohomology.cohomologyLocusDivisorUniqueness k)
  have hP : B.Contains P.X.left := contains_of_degreeLocus B (B.inclusion.map f)
    (topologicalKrullDim_fiber_le_one_of_isCurve k _) σ hσ P e hk
    (fun d => (h1 d).2.1.toQuasiCompact)
    (fun d => have := (h1 d).2.2.1
      have := SmoothOfRelativeDimension.smooth (genus (B.inclusion.map f))
        ((degreeLocus (B.inclusion.map f) (topologicalKrullDim_fiber_le_one_of_isCurve k _) σ hσ P e
          d).ι ≫ P.X.hom)
      inferInstance)
  exact (picardFunctorRepresentableBy B hX hk f σ hσ P e hP
    (fun U => isIso_bcProj_c (B.inclusion.map f) σ hσ (siteOver B hk U))).isRepresentable

end Stacks.RigidifiedPicard

end
