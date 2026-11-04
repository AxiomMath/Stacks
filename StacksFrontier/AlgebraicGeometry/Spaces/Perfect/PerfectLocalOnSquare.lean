module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceStrictlyPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleStructureSheafPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModelsGeneral

/-!
# Perfectness is local on the small étale site of an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `{f_i : Y_i ⟶ X}` be a family of étale
morphisms of algebraic spaces which is jointly surjective on points.  An object `K` of `D(𝒪_X)`
whose restrictions `f_i^*K` are all perfect is perfect.  Read for the two morphisms
`U ⟶ X ⟵ V` of an elementary distinguished square, which are jointly surjective because the
étale morphism is an isomorphism over the complement of the open subspace, this is the first
sentence of the source's proof of Stacks 08HK: "being perfect is local on `X_étale`, thus it
suffices to check that `Rj_*E` is perfect when restricted to `U` and `V`".

## Main results

* `AlgebraicGeometry.Space.SmallEtale.mem_topology_of_forall_postcomp`: a sieve on an étale chart
  of `X` covers it as soon as its pullback to every composite chart `Y_i ⟶ X` it receives
  covers that composite chart.
* `AlgebraicGeometry.Space.mem_range_pointsMap_or_of_isElementaryDistinguishedSquare`: the two
  morphisms of an elementary distinguished square are jointly surjective on points.
* `AlgebraicGeometry.Space.exists_quasiIso_restrictComplex_postcomp`: a strictly perfect local
  model of `f^*L` over a chart `Z` of `Y` gives one of `L` over the composite chart of `X`.
* `AlgebraicGeometry.Space.isPerfect_of_isPerfect_etaleModulePullback`: perfectness descends
  along a jointly surjective family of étale morphisms.
* `AlgebraicGeometry.Space.isPerfect_of_isPerfect_edsDerivedRestrict`: perfectness descends
  along the two morphisms of an elementary distinguished square.

## Implementation notes

*The covering.*  A chart `A` of `X` is covered by the composite charts `f_i(Z) ⟶ A`: a point of
the scheme of `A` has image in `|X|` lying under a point of some `Y_i`, which lies under a point
of an étale chart `Z₀` of `Y_i`, and Stacks 03H4 produces a point of the fibre product
`A ×_X Z₀` over both.  That fibre product is a scheme étale over the scheme of `Z₀`, so it is an
étale chart of `Y_i`, and postcomposed with `f_i` it maps to `A`.  The covering property is then
checked pointwise, by `AlgebraicGeometry.Space.SmallEtale.mem_topology_iff_exists_mem_range`.

*The local models.*  Perfectness of `K` is witnessed by an arbitrary representative `L`, every
representative of a perfect object being a perfect complex
(`AlgebraicGeometry.RingedSite.isPerfectComplex_of_isPerfect`, which rests on Stacks 08FR at
independent universes).  Over a chart `Z` of `Y_i` the restriction of `f_i^*L` *is*, on the nose,
the reindexing of the restriction of `L` to the composite chart along the slice equivalence of
Stacks 04M0, `AlgebraicGeometry.Space.smallEtaleRingedSitePostcompOverEquivalence`; so a local
model on the side of `Y_i` is carried to one on the side of `X` by
`Stacks.SheafOfModules.exists_quasiIso_of_reindex`.  Postcomposition is cover preserving, which
moves the covering sieve of `Z` to one of its composite chart.

## References

* [Stacks Project, Tag 08HK](https://stacks.math.columbia.edu/tag/08HK)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The composite charts of a jointly surjective étale family cover -/

/-- **A point of a chart lies under a composite chart of a member of an étale family through
whose image its point of `|X|` passes.**  If the image in `|X|` of a point `x` of the scheme of
an étale chart `A` of `X` lies in the image of `|Y| ⟶ |X|` for an étale `f : Y ⟶ X`, then some
étale chart `Z` of `Y`, postcomposed with `f`, maps to `A` with `x` in the image of the
underlying scheme morphism. -/
theorem SmallEtale.exists_postcomp_hom_mem_range {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (A : SmallEtale B S hS X.1)
    (a : points B S hS (yoneda.obj A.obj.left))
    (ha : pointsMap B S hS _ A.obj.hom a ∈ Set.range (pointsMap B S hS Y.1 f.hom)) :
    ∃ (Z : SmallEtale B S hS Y.1) (g : (smallEtalePostcomp B S hS f hf).obj Z ⟶ A),
      pointsToScheme B S hS _ a ∈ Set.range ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS X.1).map g)) := by
  obtain ⟨y, hy⟩ := ha
  obtain ⟨Z₀, z, hz⟩ := exists_chart_point B S hS Y.1 Y.2 y
  set C := (smallEtalePostcomp B S hS f hf).obj Z₀
  have hC : pointsMap B S hS _ A.obj.hom a = pointsMap B S hS _ C.obj.hom z := by
    show _ = pointsMap B S hS _ (Z₀.obj.hom ≫ f.hom) z
    rw [pointsMap_comp_apply, hz, hy]
  obtain ⟨w, hw, -⟩ := exists_point_of_isPullback_presheaf B S hS
    (A.property.rep.isPullback' C.obj.hom) a z hC
  let Z : SmallEtale B S hS Y.1 :=
    ⟨CostructuredArrow.mk (yoneda.map (A.property.rep.snd C.obj.hom) ≫ Z₀.obj.hom),
      etale_comp_of_scheme B S hS _ Z₀.obj.hom (A.property.property_snd C.obj.hom)
        Z₀.property⟩
  refine ⟨Z, ObjectProperty.homMk (CostructuredArrow.homMk (A.property.rep.fst' C.obj.hom)
    (A.property.rep.isPullback' C.obj.hom).w), pointsToScheme B S hS _ w, ?_⟩
  rw [← hw, pointsToScheme_pointsMap_yoneda]
  rfl

/-- **The composite charts of a jointly surjective étale family cover.**  Let `{f_i : Y_i ⟶ X}`
be étale morphisms of algebraic spaces whose images cover `|X|`, and let `R` be a sieve on an
étale chart `A` of `X`.  If for every étale chart `Z` of some `Y_i` and every morphism
`g : f_i(Z) ⟶ A` the pullback of `R` along `g` covers `f_i(Z)`, then `R` covers `A`. -/
theorem SmallEtale.mem_topology_of_forall_postcomp {X : AlgebraicSpaces B S hS} {ι : Type*}
    {Y : ι → AlgebraicSpaces B S hS} (f : ∀ i, Y i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)
    (hsurj : ∀ x : points B S hS X.1, ∃ i, x ∈ Set.range (pointsMap B S hS (Y i).1 (f i).hom))
    (A : SmallEtale B S hS X.1) (R : Sieve A)
    (hR : ∀ (i : ι) (Z : SmallEtale B S hS (Y i).1)
      (g : (smallEtalePostcomp B S hS (f i) (hf i)).obj Z ⟶ A),
      R.pullback g ∈
        SmallEtale.topology B S hS X.1 ((smallEtalePostcomp B S hS (f i) (hf i)).obj Z)) :
    R ∈ SmallEtale.topology B S hS X.1 A := by
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro x
  obtain ⟨a, rfl⟩ := surjective_pointsToScheme B S hS _ x
  obtain ⟨i, hi⟩ := hsurj (pointsMap B S hS _ A.obj.hom a)
  obtain ⟨Z, g, z, hz⟩ := exists_postcomp_hom_mem_range B S hS (f i) (hf i) A a hi
  obtain ⟨V, h, hh, z', hz'⟩ :=
    (SmallEtale.mem_topology_iff_exists_mem_range B S hS _ _).1 (hR i Z g) z
  refine ⟨V, h ≫ g, hh, z', ?_⟩
  rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, hz', hz]
  rfl

/-- **The two morphisms of an elementary distinguished square are jointly surjective on
points.**  A point of `|X|` outside the open subspace lies on its reduced closed complement, over
which the étale morphism of the square is an isomorphism, so it lifts. -/
theorem mem_range_pointsMap_or_of_isElementaryDistinguishedSquare
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hW : IsAlgebraicSpace B S hS W} {U : Subfunctor W}
    {f : V ⟶ W} (hsq : IsElementaryDistinguishedSquare B S hS hW U f) (x : points B S hS W) :
    x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) ∨
      x ∈ Set.range (pointsMap B S hS V f) := by
  by_cases hx : x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι)
  · exact Or.inl hx
  refine Or.inr ?_
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  have hmem := (FieldValuedPoint.mem_obj_reducedClosedSubspace_iff_class_mem B S hS hW
    (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ hsq.isClosedComplement p).2 hx
  have := hsq.isIsoOverComplement
  have hbij := (isIso_iff_bijective ((Subfunctor.fromPreimage (reducedClosedSubspace B S hS W hW
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ hsq.isClosedComplement) f).app
    (Opposite.op (p.siteObject B S hS W)))).1 inferInstance
  obtain ⟨y, hy⟩ := hbij.2 ⟨p.value, hmem⟩
  refine ⟨(⟨p.carrier, p.contained, p.toBase, y.1⟩ : FieldValuedPoint B S hS V).class B S hS V,
    ?_⟩
  rw [pointsMap_class]
  exact congrArg (fun v => (⟨p.carrier, p.contained, p.toBase, v⟩ :
    FieldValuedPoint B S hS W).class B S hS W) (congrArg Subtype.val hy)

/-! ### Local models along an étale morphism -/

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- **A strictly perfect local model of an étale restriction is one of the complex itself.**  Let
`f : Y ⟶ X` be étale and `L` a complex of `𝒪_X`-modules.  If over an étale chart `Z` of `Y` a
strictly perfect complex maps quasi-isomorphically to the restriction of `f^*L`, then over the
composite chart `f(Z)` of `X` a strictly perfect complex maps quasi-isomorphically to the
restriction of `L`.

The restriction of `f^*L` to `Z` is the reindexing of the restriction of `L` to `f(Z)` along the
slice equivalence of Stacks 04M0, so this is `Stacks.SheafOfModules.exists_quasiIso_of_reindex`. -/
theorem exists_quasiIso_restrictComplex_postcomp {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (L : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (Z : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
    (h : ∃ P : CochainComplex (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).over Z)) ℤ,
      IsStrictlyPerfect
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).over Z) P ∧
        ∃ q : P ⟶ (smallEtaleRingedSite B S hS Y.1 Y.2).restrictComplex
          (((etaleModulePullback.{u, u} B S hS f hf).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) Z, QuasiIso q) :
    ∃ P : CochainComplex (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over
          ((smallEtaleRingedSitePostcomp B S hS f hf).obj Z))) ℤ,
      IsStrictlyPerfect
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over
          ((smallEtaleRingedSitePostcomp B S hS f hf).obj Z)) P ∧
        ∃ q : P ⟶ (smallEtaleRingedSite B S hS X.1 X.2).restrictComplex L
          ((smallEtaleRingedSitePostcomp B S hS f hf).obj Z), QuasiIso q := by
  obtain ⟨P, hP, q, hq⟩ := h
  have : (Stacks.SheafOfModules.reindexEquivalence.{u, u}
      (J' := (smallEtaleRingedSite B S hS Y.1 Y.2).J.over Z)
      (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf Z)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj Z))).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let c : (smallEtaleRingedSite B S hS Y.1 Y.2).restrictComplex
        (((etaleModulePullback.{u, u} B S hS f hf).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) Z ≅
      (((Stacks.SheafOfModules.reindexEquivalence.{u, u}
        (J' := (smallEtaleRingedSite B S hS Y.1 Y.2).J.over Z)
        (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf Z)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over
          ((smallEtaleRingedSitePostcomp B S hS f hf).obj Z))).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
        ((smallEtaleRingedSite B S hS X.1 X.2).restrictComplex L
          ((smallEtaleRingedSitePostcomp B S hS f hf).obj Z))) :=
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => rfl)
  have := hq
  have : IsIso c.hom := c.isIso_hom
  have : QuasiIso c.hom := quasiIso_of_isIso c.hom
  have : QuasiIso (q ≫ c.hom) := quasiIso_comp q c.hom
  exact Stacks.SheafOfModules.exists_quasiIso_of_reindex
    (J' := (smallEtaleRingedSite B S hS Y.1 Y.2).J.over Z)
    (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf Z)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over
      ((smallEtaleRingedSitePostcomp B S hS f hf).obj Z))
    ((smallEtaleRingedSite B S hS X.1 X.2).restrictComplex L
      ((smallEtaleRingedSitePostcomp B S hS f hf).obj Z)) hP (q ≫ c.hom) this

/-! ### Perfectness descends along a jointly surjective étale family -/

/-- **Perfectness is local on the small étale site.**  Let `{f_i : Y_i ⟶ X}` be étale morphisms
of algebraic spaces whose images cover `|X|`, and let `K` be an object of `D(𝒪_X)`.  If every
restriction `f_i^*K` is a perfect object of `D(𝒪_{Y_i})`, then `K` is a perfect object of
`D(𝒪_X)`.

A representative `L` of `K` is shown to be a perfect complex.  Over a chart `A` of `X` the
arrows into `A` from charts carrying a local model of `L` form a covering sieve: it is enough to
check this after pulling back to each composite chart `f_i(Z) ⟶ A`
(`AlgebraicGeometry.Space.SmallEtale.mem_topology_of_forall_postcomp`), and there the covering
sieve of `Z` carrying the local models of the perfect complex `f_i^*L` is pushed forward along
postcomposition and its models are carried across
(`AlgebraicGeometry.Space.exists_quasiIso_restrictComplex_postcomp`). -/
theorem isPerfect_of_isPerfect_etaleModulePullback {X : AlgebraicSpaces B S hS} {ι : Type*}
    {Y : ι → AlgebraicSpaces B S hS} (f : ∀ i, Y i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)
    (hsurj : ∀ x : points B S hS X.1, ∃ i, x ∈ Set.range (pointsMap B S hS (Y i).1 (f i).hom))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : ∀ i, (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).IsPerfect
      ((etaleModulePullback.{u, u} B S hS (f i) (hf i)).mapDerivedCategory.obj K)) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect K := by
  classical
  obtain ⟨L, eL⟩ : Σ' L : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ,
      DerivedCategory.Q.obj L ≅ K :=
    ⟨DerivedCategory.Q.objPreimage K, DerivedCategory.Q.objObjPreimageIso K⟩
  -- Every restriction of `L` is a perfect complex.
  have hN : ∀ i, (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).IsPerfectComplex
      (((etaleModulePullback.{u, u} B S hS (f i) (hf i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) := fun i =>
    RingedSite.isPerfectComplex_of_isPerfect _ (hK i) _
      (((etaleModulePullback.{u, u} B S hS (f i) (hf i)).mapDerivedCategoryFactors.app L).symm ≪≫
        (etaleModulePullback.{u, u} B S hS (f i) (hf i)).mapDerivedCategory.mapIso eL)
  refine ⟨L, fun A => ?_, ⟨eL⟩⟩
  refine ⟨fun {A'} _ => ∃ P : CochainComplex (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over A'))
      ℤ, IsStrictlyPerfect
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over A')
        P ∧ ∃ q : P ⟶ (smallEtaleRingedSite B S hS X.1 X.2).restrictComplex L A', QuasiIso q,
    ?_, fun _ _ hg => hg⟩
  refine SmallEtale.mem_topology_of_forall_postcomp B S hS f hf hsurj A _ fun i Z g => ?_
  obtain ⟨S₀, hS₀, hmodels⟩ := hN i Z
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_
    ((SmallEtale.coverPreserving_smallEtalePostcomp B S hS (f i) (hf i)).cover_preserve hS₀)
  rintro A'' h ⟨Z', b, k, hb, rfl⟩
  obtain ⟨Z'', b₁, s, hs, rfl⟩ := hb
  -- The local model over `Z'`, restricted from the one over the source of `s`.
  have hZ' := RingedSite.exists_localModel_restrictComplex_of_hom _ _ b₁ (hmodels s hs)
  have hfZ' := exists_quasiIso_restrictComplex_postcomp B S hS (f i) (hf i) L Z' hZ'
  exact ⟨_, 𝟙 _, k ≫ (smallEtalePostcomp B S hS (f i) (hf i)).map (b₁ ≫ s) ≫ g,
    RingedSite.exists_localModel_restrictComplex_of_hom _ L k hfZ', Category.id_comp _⟩

/-! ### Perfectness descends along an elementary distinguished square -/

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **Perfectness descends along an elementary distinguished square.**  Let `(U ⊆ X, j : V ⟶ X)`
be an elementary distinguished square of algebraic spaces over `S` and let `E` be an object of
`D(𝒪_X)`.  If `E|_U` is perfect in `D(𝒪_U)` and `E|_V` is perfect in `D(𝒪_V)`, then `E` is
perfect in `D(𝒪_X)`.

This is the locality of perfectness on `X_étale` used in the first sentence of the source's proof
of Stacks 08HK: the open immersion and the étale morphism of the square are jointly surjective on
points (`AlgebraicGeometry.Space.mem_range_pointsMap_or_of_isElementaryDistinguishedSquare`), so
`AlgebraicGeometry.Space.isPerfect_of_isPerfect_etaleModulePullback` applies. -/
theorem isPerfect_of_isPerfect_edsDerivedRestrict
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hU : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2).IsPerfect
      ((edsDerivedRestrictOpen B S hS hsq).obj E))
    (hV : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2).IsPerfect
      ((edsDerivedRestrictEtale B S hS hsq).obj E)) :
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect E := by
  refine isPerfect_of_isPerfect_etaleModulePullback B S hS
    (Y := fun b : Bool => if b then edsOpen B S hS hsq else edsEtale B S hS hsq)
    (fun b => match b with
      | true => edsOpenHom B S hS hsq
      | false => edsEtaleHom B S hS hsq)
    (fun b => match b with
      | true => isEtale_edsOpenHom B S hS hsq
      | false => isEtale_edsEtaleHom B S hS hsq) ?_ E ?_
  · intro x
    rcases mem_range_pointsMap_or_of_isElementaryDistinguishedSquare B S hS hsq x with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  · intro b
    cases b
    · exact hV
    · exact hU

end Square

end AlgebraicGeometry.Space

end
