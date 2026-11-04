module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.SquareLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Approximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ChartLocalPerfectness
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos

/-!
# Étale restriction of derived objects of an algebraic space

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces and `E` an object of `D(𝒪_Y)`. The
restriction `E|_X` is perfect when `E` is, and the support of each of its cohomology sheaves is
the inverse image of the support of the corresponding cohomology sheaf of `E`. For an elementary
distinguished square `(U ⊆ W, j : V ⟶ W)` the restrictions to `U` and `V` detect supports, and
they detect when a morphism of `𝒪_W`-modules is an isomorphism or an epimorphism.

## Main results

* `AlgebraicGeometry.Space.isPerfect_etaleRestrict`: étale restriction preserves perfectness.
* `AlgebraicGeometry.Space.supportOfSheaf_homology_etaleRestrict`: the support of a cohomology
  sheaf of a restriction is an inverse image.
* `AlgebraicGeometry.Space.range_union_range_eds`: the points of `U` and of `V` cover `W`.
* `AlgebraicGeometry.Space.supportOfSheaf_subset_of_eds`: a support condition holds on `W` once
  it holds on `U` and on `V`.
* `AlgebraicGeometry.Space.isIso_of_eds`, `AlgebraicGeometry.Space.epi_of_eds`: isomorphisms
  and epimorphisms of modules are detected on `U` and `V`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Restrict

variable {X Y : AlgebraicSpaces B S hS}

/-- **Étale restriction preserves perfectness**: for `f : X ⟶ Y` étale and `E` perfect in
`D(𝒪_Y)`, the restriction `E|_X` is perfect. It is the derived pullback `Lf^*E`. -/
theorem isPerfect_etaleRestrict (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hE : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect E) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect
      ((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory.obj E) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := isPerfect_smallEtaleDerivedModulePullback f E hE
  exact ⟨K, hK, ⟨e ≪≫ (smallEtaleDerivedModulePullbackIsoEtale B S hS f hf).app E⟩⟩

/-- Perfectness is invariant under isomorphism in `D(𝒪_X)`. -/
theorem isPerfect_of_iso {E E' : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)}
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E) (e : E ≅ E') :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E' := by
  obtain ⟨K, hK, ⟨e'⟩⟩ := hE
  exact ⟨K, hK, ⟨e' ≪≫ e⟩⟩

open ZeroObject in
/-- A zero object of `D(𝒪_X)` is perfect: on every chart it has the zero complex as a strictly
perfect model. -/
theorem isPerfect_of_isZero {E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} (hE : IsZero E) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E := by
  refine isPerfect_of_hasStrictlyPerfectModel_chart _ fun U => ⟨⊤, by simp, fun V _ _ => ?_⟩
  have h0 : ∀ i, IsZero ((0 : CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) ℤ).X i) := fun i =>
    (HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)
  refine ⟨0, fun j => ⟨0, 0, 0, (h0 j).eq_of_src _ _⟩, ⟨0, 0, ?_, ?_⟩, ⟨?_⟩⟩
  · exact (CochainComplex.isStrictlyGE_iff _ 0).2 fun i _ => h0 i
  · exact (CochainComplex.isStrictlyLE_iff _ 0).2 fun i _ => h0 i
  · exact IsZero.iso (Functor.map_isZero _ hE) (Functor.map_isZero _ (isZero_zero _))

/-- **The support of a cohomology sheaf of an étale restriction is an inverse image**: for
`f : X ⟶ Y` étale, `Supp Hⁱ(E|_X) = |f|⁻¹ Supp Hⁱ(E)`. -/
theorem supportOfSheaf_homology_etaleRestrict (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) (i : ℤ) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
          ((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory.obj E))) =
      pointsMap B S hS X.1 f.hom ⁻¹' supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj E)) := by
  rw [← supportOfSheaf_toSheaf_etaleModulePullback B S hS f hf]
  have key : ∀ {F G : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}} (e : F ≅ G),
      supportOfSheaf B S hS X.1 F = supportOfSheaf B S hS X.1 G := fun e =>
    Set.eq_of_subset_of_subset (supportOfSheaf_subset_of_mono B S hS X.1 X.2 e.hom)
      (supportOfSheaf_subset_of_mono B S hS X.1 X.2 e.inv)
  exact key ((SheafOfModules.toSheaf _).mapIso
    (((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategoryHomologyIso i).app E))

/-- If `E` is supported on `T ⊆ |Y|`, its restriction along an étale `f : X ⟶ Y` is supported
on `|f|⁻¹ T`. -/
theorem cohomologySupportedOn_etaleRestrict (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    {T : Set (points B S hS Y.1)} {E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)}
    (hE : CohomologySupportedOn B S hS Y.1 Y.2 T E) :
    CohomologySupportedOn B S hS X.1 X.2 (pointsMap B S hS X.1 f.hom ⁻¹' T)
      ((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory.obj E) := fun i =>
  (le_of_eq (supportOfSheaf_homology_etaleRestrict B S hS f hf E i)).trans
    (Set.preimage_mono (hE i))

/-- **Charts through a point of the image of an étale morphism.** Let `f : Y ⟶ X` be étale, `U`
a chart of `X` and `u` a point of `U` whose image in `|X|` is the image of a point `y` of `Y`.
Then some chart `V` of `Y` maps to `U` over `X` with `u` in the image. -/
theorem exists_chart_lift_of_isEtale (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (U : SmallEtale B S hS X.1) (u : points B S hS (yoneda.obj U.1.left))
    (y : points B S hS Y.1)
    (hy : pointsMap B S hS _ U.1.hom u = pointsMap B S hS Y.1 f.hom y) :
    ∃ (V : SmallEtale B S hS Y.1) (p : V.1.left ⟶ U.1.left),
      yoneda.map p ≫ U.1.hom = V.1.hom ≫ f.hom ∧
        pointsToScheme B S hS U.1.left u ∈
          Set.range ((BigFppfOver.toScheme B S hS).map p) := by
  have sq := IsPullback.of_hasPullback U.1.hom f.hom
  obtain ⟨q, hq1, -⟩ := exists_point_of_isPullback_presheaf B S hS sq u y hy
  have hU : IsEtale B S hS U.1.hom := (isEtale_iff_presheaf_of_yoneda B S hS _).2 U.2
  have hQ : IsAlgebraicSpace B S hS (pullback U.1.hom f.hom) :=
    isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS _) Y.2 X.2
  have hfst : IsEtale B S hS (pullback.fst U.1.hom f.hom) := by
    have h := isEtale_pullback_snd B S hS (isAlgebraicSpace_yoneda B S hS _) X.2 Y.2
      f.hom U.1.hom hf
    have e : pullback.fst U.1.hom f.hom =
        (pullbackSymmetry U.1.hom f.hom).hom ≫ pullback.snd f.hom U.1.hom := by simp
    rw [e]
    exact isEtale_comp B S hS (isEtale_of_isIso B S hS _) h
  have hsnd : IsEtale B S hS (pullback.snd U.1.hom f.hom) :=
    isEtale_pullback_snd B S hS Y.2 X.2 (isAlgebraicSpace_yoneda B S hS _) U.1.hom f.hom hU
  obtain ⟨A, a, w, ha, hw, -, -⟩ :=
    exists_etale_scheme_chart_through_point B S hS hQ (pullback.fst U.1.hom f.hom) hfst q
  have hV : IsEtaleChart B S hS Y.1 (CostructuredArrow.mk (a ≫ pullback.snd U.1.hom f.hom)) :=
    (isEtale_iff_presheaf_of_yoneda B S hS _).1 (isEtale_comp B S hS ha hsnd)
  refine ⟨⟨CostructuredArrow.mk (a ≫ pullback.snd U.1.hom f.hom), hV⟩,
    yoneda.preimage (a ≫ pullback.fst U.1.hom f.hom), ?_, ?_⟩
  · simp only [Functor.map_preimage, Category.assoc, pullback.condition]
    rfl
  · refine ⟨pointsToScheme B S hS A w, (pointsToScheme_pointsMap_yoneda B S hS _ w).symm.trans
      (congrArg _ ?_)⟩
    rw [Functor.map_preimage, pointsMap_comp]
    exact (congrArg _ hw).trans hq1

/-- **Perfectness is local along a jointly surjective family of étale morphisms**: if the
restrictions of `E` along étale morphisms `fᵢ : Yᵢ ⟶ X` whose images cover `|X|` are perfect,
then `E` is perfect. -/
theorem isPerfect_of_forall_isPerfect_etaleRestrict {ι : Type*} (Y : ι → AlgebraicSpaces B S hS)
    (f : ∀ i, Y i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)
    (hsurj : ∀ x : points B S hS X.1, ∃ i, ∃ y : points B S hS (Y i).1,
      pointsMap B S hS _ (f i).hom y = x)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : ∀ i, (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).IsPerfect
      ((etaleModulePullback.{u, u} B S hS (f i) (hf i)).mapDerivedCategory.obj E)) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E := by
  refine isPerfect_of_hasStrictlyPerfectModel_chart _ fun U => ?_
  let R : Presieve U := fun V _ => HasStrictlyPerfectModel B S hS
    ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E)
  refine ⟨R, ?_, fun V g hg => hg⟩
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro z
  obtain ⟨u, rfl⟩ := surjective_pointsToScheme B S hS U.1.left z
  obtain ⟨i, y, hy⟩ := hsurj (pointsMap B S hS _ U.1.hom u)
  obtain ⟨V, p, hp, w, hw⟩ := exists_chart_lift_of_isEtale B S hS (f i) (hf i) U u y hy.symm
  have hEi : (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).IsPerfect
      ((smallEtaleDerivedModulePullback B S hS (f i)).obj E) :=
    isPerfect_of_iso B S hS (hE i)
      ((smallEtaleDerivedModulePullbackIsoEtale B S hS (f i) (hf i)).app E).symm
  obtain ⟨R₀, hR₀, hR₀mod⟩ := exists_hasStrictlyPerfectModel_chart_of_isPerfect _ hEi V
  obtain ⟨W', m, ⟨W'', m', m'', hm'', rfl⟩, w', hw'⟩ :=
    (SmallEtale.mem_topology_iff_exists_mem_range B S hS (Y i).1 _).1 hR₀ w
  let Wx : SmallEtale B S hS X.1 := (smallEtalePostcomp B S hS (f i) (hf i)).obj W''
  have hm''w : yoneda.map ((SmallEtale.toOver B S hS (Y i).1).map m'') ≫ V.1.hom = W''.1.hom :=
    CostructuredArrow.w m''.hom
  let gx : Wx ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk
    ((SmallEtale.toOver B S hS (Y i).1).map m'' ≫ p) (by
      show yoneda.map (_ ≫ p) ≫ U.1.hom = W''.1.hom ≫ (f i).hom
      rw [Functor.map_comp, Category.assoc, hp, ← Category.assoc, hm''w]))
  have hc : chartToSpace B S hS (Y i) W'' ≫ f i = chartToSpace B S hS X Wx := rfl
  refine ⟨Wx, gx, Sieve.le_generate R _ _ ?_, ?_⟩
  · exact (hR₀mod m'' hm'').of_iso
      ((smallEtaleDerivedModulePullbackCompIso B S hS (chartToSpace B S hS (Y i) W'')
        (f i)).app E ≪≫ (smallEtaleDerivedModulePullbackCongr B S hS hc).app E)
  · refine ⟨(BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS (Y i).1).map m') w',
      ?_⟩
    show (BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS (Y i).1).map m'' ≫ p) _ = _
    rw [← hw, ← hw', Functor.map_comp, Functor.map_comp, Functor.map_comp,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]

end Restrict

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **The points of `U` and of `V` cover `W`** in an elementary distinguished square: a point
outside `U` lies in the reduced closed complement, over which `V ⟶ W` is an isomorphism. -/
theorem range_union_range_eds :
    Set.range (pointsMap B S hS (edsOpen B S hS hsq).1 (edsOpenHom B S hS hsq).hom) ∪
      Set.range (pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom) =
        Set.univ := by
  classical
  let C := (Set.range (pointsMap B S hS Uo.toFunctor Uo.ι))ᶜ
  let Z := reducedClosedSubspace B S hS W.1 W.2 C hsq.isClosedComplement
  have hZsupport : Set.range (pointsMap B S hS Z.toFunctor Z.ι) = C :=
    range_pointsMap_ι_reducedClosedSubspace B S hS W.1 W.2 C hsq.isClosedComplement
  have : IsIso (Z.fromPreimage fV) := hsq.isIsoOverComplement
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
  by_cases hx : x ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)
  · exact Or.inl hx
  · obtain ⟨z, hz⟩ : x ∈ Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
      rwa [hZsupport]
    obtain ⟨y, hy⟩ : ∃ y, pointsMap B S hS _ (Z.fromPreimage fV) y = z :=
      ⟨pointsMap B S hS _ (inv (Z.fromPreimage fV)) z, by
        show (pointsMap B S hS _ (Z.fromPreimage fV) ∘ pointsMap B S hS _
          (inv (Z.fromPreimage fV))) z = z
        rw [← pointsMap_comp, IsIso.inv_hom_id, pointsMap_id, id]⟩
    refine Or.inr ⟨pointsMap B S hS (Z.preimage fV).toFunctor (Z.preimage fV).ι y, ?_⟩
    show (pointsMap B S hS V fV ∘ pointsMap B S hS (Z.preimage fV).toFunctor
      (Z.preimage fV).ι) y = x
    rw [← pointsMap_comp, ← Subfunctor.fromPreimage_ι Z fV, pointsMap_comp]
    exact (congrArg _ hy).trans hz

/-- **A support condition is local for an elementary distinguished square**: if the support of
the restriction of an abelian sheaf to `U` and to `V` lies over `T`, so does its support. -/
theorem supportOfSheaf_subset_of_eds (F : Modules.{u, u} B S hS W.1 W.2)
    (T : Set (points B S hS W.1))
    (hU : supportOfSheaf B S hS (edsOpen B S hS hsq).1 ((SheafOfModules.toSheaf _).obj
      ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).obj F)) ⊆
      pointsMap B S hS _ (edsOpenHom B S hS hsq).hom ⁻¹' T)
    (hV : supportOfSheaf B S hS (edsEtale B S hS hsq).1 ((SheafOfModules.toSheaf _).obj
      ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj F)) ⊆
      pointsMap B S hS _ (edsEtaleHom B S hS hsq).hom ⁻¹' T) :
    supportOfSheaf B S hS W.1 ((SheafOfModules.toSheaf _).obj F) ⊆ T := by
  rw [supportOfSheaf_toSheaf_etaleModulePullback] at hU hV
  intro x hx
  rcases Set.eq_univ_iff_forall.mp (range_union_range_eds B S hS hsq) x with
    ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact hU hx
  · exact hV hx

/-- The cokernel of a morphism of modules vanishes if its restrictions to `U` and `V` are
epimorphisms. -/
private theorem isZero_cokernel_of_epi_eds {F G : Modules.{u, u} B S hS W.1 W.2} (φ : F ⟶ G)
    (hU : Epi ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).map φ))
    (hV : Epi ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).map φ)) : IsZero (cokernel φ) := by
  refine isZero_of_isZero_restrict_eds B S hS hsq _ ?_ ?_
  · exact (isZero_cokernel_of_epi _).of_iso
      (PreservesCokernel.iso (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)) φ)
  · exact (isZero_cokernel_of_epi _).of_iso
      (PreservesCokernel.iso (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)) φ)

/-- **Isomorphisms of modules are detected on an elementary distinguished square.** -/
theorem isIso_of_eds {F G : Modules.{u, u} B S hS W.1 W.2} (φ : F ⟶ G)
    (hU : IsIso ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).map φ))
    (hV : IsIso ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).map φ)) : IsIso φ := by
  let LU := etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)
  let LV := etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)
  have hK : IsZero (kernel φ) := by
    refine isZero_of_isZero_restrict_eds B S hS hsq _ ?_ ?_
    · exact (isZero_kernel_of_mono (LU.map φ)).of_iso (PreservesKernel.iso LU φ)
    · exact (isZero_kernel_of_mono (LV.map φ)).of_iso (PreservesKernel.iso LV φ)
  have : Mono φ := Preadditive.mono_of_isZero_kernel _ hK
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _ (isZero_cokernel_of_epi_eds B S hS hsq φ
    inferInstance inferInstance)
  exact isIso_of_mono_of_epi φ

/-- **Epimorphisms of modules are detected on an elementary distinguished square.** -/
theorem epi_of_eds {F G : Modules.{u, u} B S hS W.1 W.2} (φ : F ⟶ G)
    (hU : Epi ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).map φ))
    (hV : Epi ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).map φ)) : Epi φ :=
  Preadditive.epi_of_isZero_cokernel _ (isZero_cokernel_of_epi_eds B S hS hsq φ hU hV)

end Square

end AlgebraicGeometry.Space

end
