module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.InvariantAffineOpen
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FiniteLocallyFreePushPull
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.CommonAffineOpenOfDimensionOnePointsFiniteComponents

/-!
# A finite locally free cover by a scheme makes a neighbourhood of a fibre a scheme

This file is Step 3 of the proof of Stacks 0ADD sketched in Stacks 0ADE.  Let `X` be a
separated, locally Noetherian algebraic space over `S`, let `x ∈ |X|` be a point whose local
ring has dimension at most one, let `g : X' ⟶ X` be a finite morphism of algebraic spaces and
let `h : Y' ⟶ X'` be a surjective finite locally free morphism whose source `Y'` is a scheme.
Then there is an open subspace `O ⊆ X'` containing every point of `X'` lying over `x` which is a
scheme.

The source says: "`X'` is a scheme because `Y'` is a scheme, `Y' ⟶ X'` is finite locally free,
and every finite set of codimension `1` points of `Y'` is contained in an affine open; use
Properties of Spaces, Proposition 07S6 and Varieties, Proposition 09NN."  That is the argument
here.  The points of `Y'` over `x` form a finite set (the composite `Y' ⟶ X` is finite) whose
local rings have dimension at most one (Stacks 0ABW), and `Y'` is separated and locally
Noetherian, so by Stacks 09NN they lie in one affine open `A ⊆ Y'`.  The complement in `|X'|`
of the image of `|Y'| ∖ |A|` is open, because `h` is finite, and contains every point over `x`;
over it, `h` restricts to a surjective finite locally free morphism from an open subscheme of the
affine `A`, every finite subset of which therefore lies in an affine open (prime avoidance).  The
quotient construction of Stacks 07S6, in the form
`AlgebraicGeometry.Space.isRepresentable_of_presheafSurjective_presheafFiniteLocallyFree`, then
makes that open subspace a scheme.

## Main results

* `AlgebraicGeometry.Space.exists_restrict_yoneda_of_isOpenSubspace`: the restriction of a
  morphism out of a scheme of the site over an open subspace of its target, as an open
  subscheme of the source sitting in a cartesian square.
* `AlgebraicGeometry.Space.finite_preimage_singleton_of_isFinite`: a finite morphism of
  algebraic spaces has finite fibres.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_isFiniteLocallyFree_cover`:
  **Step 3 of Stacks 0ADE**, the statement above.

## References

* [Stacks Project, Tag 0ADE](https://stacks.math.columbia.edu/tag/0ADE)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
* [Stacks Project, Tag 09NN](https://stacks.math.columbia.edu/tag/09NN)
* [Stacks Project, Tag 0ABW](https://stacks.math.columbia.edu/tag/0ABW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A finite subset of an open subscheme of an affine open lies in an affine open of it.**
Let `j : W ⟶ Y` be an open immersion of schemes whose image lies in an affine open `A` of `Y`.
Then every finite set of points of `W` lies in an affine open of `W`.  This is prime avoidance
in `Γ(A)`, `AlgebraicGeometry.exists_basicOpen_of_finite_subset`, transported along the
open immersions. -/
theorem exists_isAffineOpen_superset_of_finite_of_range_le {W Y : Scheme.{u}} (j : W ⟶ Y)
    [IsOpenImmersion j] (A : Y.Opens) (hA : IsAffineOpen A) (hjA : Set.range j ⊆ A)
    (E : Set W) (hE : E.Finite) :
    ∃ O : W.Opens, IsAffineOpen O ∧ E ⊆ O := by
  have : IsAffine A := hA
  -- the open `V ⊆ A` which is the image of `W`, as an open of the scheme `A`
  let V : (A : Scheme.{u}).Opens := A.ι ⁻¹ᵁ j.opensRange
  let K : Set (A : Scheme.{u}) := A.ι ⁻¹' (j '' E)
  have hK : K.Finite := (hE.image j).preimage A.ι.isOpenEmbedding.injective.injOn
  have hKV : K ⊆ V := by
    rintro a ⟨e, -, he⟩
    exact ⟨e, he⟩
  obtain ⟨r, hKr, hrV⟩ := exists_basicOpen_of_finite_subset hK V hKV
  -- the affine open `D(r)` of `A`, pushed into `Y` and pulled back into `W`
  let D : Y.Opens := A.ι ''ᵁ ((A : Scheme.{u}).basicOpen r)
  have hD : IsAffineOpen D :=
    ((isAffineOpen_top (A : Scheme.{u})).basicOpen r).image_of_isOpenImmersion A.ι
  have hDj : D ≤ j.opensRange := by
    rintro _ ⟨a, ha, rfl⟩
    exact hrV ha
  refine ⟨j ⁻¹ᵁ D, hD.preimage_of_isOpenImmersion j hDj, fun e he => ?_⟩
  obtain ⟨a, ha⟩ : j e ∈ Set.range A.ι := by
    rw [Scheme.Opens.range_ι]
    exact hjA ⟨e, rfl⟩
  exact ⟨a, hKr ⟨e, he, ha.symm⟩, ha⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The points of an open subscheme are the preimage of the open.**  For an open `W` of the
scheme `Y'`, the points of the open subobject on `W` are, inside `|Y'|`, the points whose image in
the scheme `Y'` lies in `W`. -/
private theorem range_pointsMap_yoneda_map_openSubobjectHom (Y' : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj Y').Opens) :
    Set.range (pointsMap B S hS _ (yoneda.map (openSubobjectHom B S hS Y' W.ι inferInstance))) =
      pointsToScheme B S hS Y' ⁻¹' W := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    rw [Set.mem_preimage, pointsToScheme_pointsMap_yoneda,
      toScheme_map_openSubobjectHom, ← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  · intro hz
    obtain ⟨q, hq⟩ : pointsToScheme B S hS Y' z ∈ Set.range W.ι := by
      rwa [Scheme.Opens.range_ι]
    let e := pointsEquivScheme B S hS (openSubobject B S hS Y' W.ι inferInstance)
    refine ⟨e.symm q, injective_pointsToScheme B S hS Y' ?_⟩
    rwa [pointsToScheme_pointsMap_yoneda, toScheme_map_openSubobjectHom,
      show pointsToScheme B S hS _ (e.symm q) = q from e.apply_symm_apply q]

/-- **The restriction of a morphism out of a scheme over an open subspace of its target.**  For
`h : h_{Y'} ⟶ X'` and an open subspace `O ⊆ X'`, the open subscheme of `Y'` on the points
mapping into `|O|` is an object `Yo` of the site, with an open immersion `j : Yo ⟶ Y'`, a
factorization `τ : h_{Yo} ⟶ O` of `j ≫ h`, and a cartesian square
`h_{Yo} = h_{Y'} ×_{X'} O`.  The image of `j` is the image, in the scheme `Y'`, of the preimage of
`|O|`. -/
theorem exists_restrict_yoneda_of_isOpenSubspace {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (Y' : BigFppfOver B S hS) (h : yoneda.obj Y' ⟶ X')
    (O : Subfunctor X') (hO : IsOpenSubspace B S hS O) :
    ∃ (Yo : BigFppfOver B S hS) (j : Yo ⟶ Y') (τ : yoneda.obj Yo ⟶ O.toFunctor),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      IsPullback (yoneda.map j) τ h O.ι ∧
      Set.range ((BigFppfOver.toScheme B S hS).map j) =
        pointsToScheme B S hS Y' '' (pointsMap B S hS _ h ⁻¹'
          Set.range (pointsMap B S hS O.toFunctor O.ι)) := by
  set P := pointsMap B S hS _ h ⁻¹' Set.range (pointsMap B S hS O.toFunctor O.ι)
  have hPopen : IsOpen P :=
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS O.ι hO.2).preimage
      (continuous_pointsMap B S hS h)
  let W : ((BigFppfOver.toScheme B S hS).obj Y').Opens :=
    ⟨schemePointsHomeomorph B S hS Y' '' P, (schemePointsHomeomorph B S hS Y').isOpenMap _ hPopen⟩
  let Wo : BigFppfOver B S hS := openSubobject B S hS Y' W.ι inferInstance
  let jW : Wo ⟶ Y' := openSubobjectHom B S hS Y' W.ι inferInstance
  have hTjW : (BigFppfOver.toScheme B S hS).map jW = W.ι :=
    toScheme_map_openSubobjectHom B S hS Y' W.ι inferInstance
  have hWo : IsAlgebraicSpace B S hS (yoneda.obj Wo) := isAlgebraicSpace_yoneda B S hS Wo
  have hA : Set.range (pointsMap B S hS (yoneda.obj Wo) (yoneda.map jW)) = P :=
    (range_pointsMap_yoneda_map_openSubobjectHom B S hS Y' W).trans
      ((schemePointsHomeomorph B S hS Y').preimage_image P)
  obtain ⟨τ, hτ⟩ := (factorsThrough_openSubspace_iff_points B S hS hX' hWo O hO
    (yoneda.map jW ≫ h)).2 (by
      rw [pointsMap_comp, Set.range_comp, hA]
      exact Set.image_preimage_subset _ _)
  have hpb : IsPullback (yoneda.map jW) τ h O.ι :=
    isPullback_of_isOpenImmersion_of_preimage_range B S hS hWo (isAlgebraicSpace_yoneda B S hS Y')
      hX' (yoneda.map jW) (isOpenImmersion_yoneda_map_openSubobjectHom B S hS Y' W.ι inferInstance)
      h O hO τ hτ.symm hA.symm
  have hjopen :
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jW) := by
    rw [hTjW]
    exact (inferInstance : _root_.AlgebraicGeometry.IsOpenImmersion W.ι)
  refine ⟨Wo, jW, τ, hjopen, hpb, ?_⟩
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨w, rfl⟩ := (pointsEquivScheme B S hS Wo).surjective t
    exact ⟨pointsMap B S hS _ (yoneda.map jW) w, hA ▸ ⟨w, rfl⟩,
      pointsToScheme_pointsMap_yoneda B S hS jW w⟩
  · rintro ⟨z, hz, rfl⟩
    rw [← hA] at hz
    obtain ⟨w, rfl⟩ := hz
    exact ⟨pointsToScheme B S hS Wo w, (pointsToScheme_pointsMap_yoneda B S hS jW w).symm⟩

/-- **A finite morphism of algebraic spaces has finite fibres.**  A finite morphism is
universally closed and locally quasi-finite, so its fibre over a field-valued point is a
quasi-compact discrete space, hence finite, and it surjects onto the set-theoretic fibre
(Stacks 03H4). -/
theorem finite_preimage_singleton_of_isFinite {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X) (φ : X' ⟶ X)
    (hφ : IsFinite B S hS φ) (x : points B S hS X) :
    (pointsMap B S hS _ φ ⁻¹' {x}).Finite := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  have hproper : IsProper B S hS φ :=
    ((isFinite_iff_isAffineHom_and_isProper B S hS hX' hX φ).mp hφ).2
  have hd := (isLocallyQuasiFinite_iff_forall_discreteTopology_fibre B S hS hX' hX φ
    (isLocallyOfFiniteType_of_isFinite B S hS hX' hX hφ)).1
    (isLocallyQuasiFinite_of_isFinite B S hS hX' hX hφ) p
  exact finite_setFibre_of_universallyClosed_of_discrete_fibre B S hS hX' hX φ
    hproper.universallyClosed p hd

/-- **A scheme of the site with a separated morphism to a separated algebraic space is
separated.**  The composite `h_U ⟶ X ⟶ S` is separated, and separatedness of a morphism out of a
representable presheaf to the final object is separatedness of the underlying scheme. -/
theorem isSeparated_toScheme_obj_of_isSeparated (hZ : B.Contains (⊤_ Scheme.{u}))
    (U : BigFppfOver B S hS) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAbsolutelySeparated B S hS hZ X) (f : yoneda.obj U ⟶ X)
    (hf : IsSeparated B S hS f) :
    ((BigFppfOver.toScheme B S hS).obj U).IsSeparated := by
  have h : IsAbsolutelySeparated B S hS hZ (yoneda.obj U) :=
    isAbsolutelySeparated_of_isSeparated B S hS hZ hX hf
  let γ : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let V : BigFppfOver B (⊤_ Scheme.{u}) hZ := (Over.map γ).obj U
  have hterm : IsTerminal (Over.mk (𝟙 (B.obj hZ)) : BigFppfOver B (⊤_ Scheme.{u}) hZ) :=
    Over.mkIdTerminal
  let e := (OverShriek.relocalizeYonedaIso γ).app U
  have h1 : IsSeparated B (⊤_ Scheme.{u}) hZ (e.hom ≫ yoneda.map (hterm.from V)) :=
    (isSeparatedOver_iff_isSeparated_of_isTerminal B (⊤_ Scheme.{u}) hZ
      (hterm.isTerminalObj yoneda _) _).1 h
  have h2 : IsSeparated B (⊤_ Scheme.{u}) hZ (yoneda.map (hterm.from V)) := by
    have hcomp := isSeparated_comp B (⊤_ Scheme.{u}) hZ e.inv _
      (isSeparated_of_isIso B (⊤_ Scheme.{u}) hZ e.inv) h1
    rwa [Iso.inv_hom_id_assoc] at hcomp
  have h3 := (isSeparated_yoneda_map_iff B (⊤_ Scheme.{u}) hZ (hterm.from V)).1 h2
  let m : (BigFppfOver.toScheme B S hS).obj U ⟶ ⊤_ Scheme.{u} :=
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (hterm.from V)
  have hm : m = terminal.from _ := terminal.hom_ext _ _
  exact ⟨hm ▸ h3⟩

/-- **A finite locally free morphism of algebraic spaces is finite.** -/
private theorem isFinite_of_presheaf_isFiniteLocallyFree {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsFinite B S hS f := by
  refine (isFinite_iff_representable B S hS f hX hY).2
    ⟨hf.rep, MorphismProperty.relative_monotone (F := yoneda) ?_ _ hf⟩
  intro A C k hk
  have : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map k) := hk
  exact Stacks.Morphisms.IsFiniteLocallyFree.isFinite _

/-- **An open subspace covered finite locally freely by part of an affine open is a scheme.**  Let
`h : h_{Y'} ⟶ X'` be surjective and finite locally free and let `O ⊆ X'` be an open subspace whose
preimage in the scheme `Y'` lies in an affine open `A`.  Then `O` is a scheme (Stacks 07S6). -/
private theorem isRepresentable_of_isOpenSubspace_of_image_subset_isAffineOpen
    {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (Y' : BigFppfOver B S hS) (h : yoneda.obj Y' ⟶ X')
    (hhsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf h)
    (hhflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf h)
    (O : Subfunctor X') (hO : IsOpenSubspace B S hS O)
    (A : ((BigFppfOver.toScheme B S hS).obj Y').Opens) (hA : IsAffineOpen A)
    (hOA : pointsToScheme B S hS Y' '' (pointsMap B S hS _ h ⁻¹'
      Set.range (pointsMap B S hS O.toFunctor O.ι)) ⊆ A) :
    O.toFunctor.IsRepresentable := by
  obtain ⟨Yo, j, τ, hjopen, hpb, hjrange⟩ :=
    exists_restrict_yoneda_of_isOpenSubspace B S hS hX' Y' h O hO
  refine isRepresentable_of_presheafSurjective_presheafFiniteLocallyFree B S hS hO.1 τ
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb hhsurj)
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb hhflf)
    fun E hE => exists_isAffineOpen_superset_of_finite_of_range_le
      ((BigFppfOver.toScheme B S hS).map j) A hA ?_ E hE
  rwa [hjrange]

/-- **Step 3 of Stacks 0ADE.**  Let `X` be a separated, locally Noetherian algebraic space over
`S`, let `x ∈ |X|` have a local ring of dimension at most one, let `g : X' ⟶ X` be finite, and let
`h : h_{Y'} ⟶ X'` be a surjective finite locally free morphism out of a scheme `Y'` of the site.
Then some open subspace of `X'` containing every point over `x` is a scheme.

The points of `Y'` over `x` are finitely many, with local rings of dimension at most one; they
lie in one affine open `A` of the separated locally Noetherian scheme `Y'` (Stacks 09NN).  Over
the open complement `O` of the image of `|Y'| ∖ |A|`, which contains every point over `x`, the
morphism `h` restricts to a surjective finite locally free morphism out of an open subscheme of
`A`, whose finite subsets lie in affine opens; Stacks 07S6 then makes `O` a scheme. -/
theorem exists_isOpenSubspace_isRepresentable_of_isFiniteLocallyFree_cover
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hX' : IsAlgebraicSpace B S hS X')
    (hsep : IsAbsolutelySeparated B S hS B.contains_terminal X)
    (hnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (x : points B S hS X) (hdim : localRingDimension B S hS x ≤ 1)
    (g : X' ⟶ X) (hg : IsFinite B S hS g) (Y' : BigFppfOver B S hS) (h : yoneda.obj Y' ⟶ X')
    (hhsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf h)
    (hhflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf h) :
    ∃ O : Subfunctor X', IsOpenSubspace B S hS O ∧ O.toFunctor.IsRepresentable ∧
      ∀ p : points B S hS X', pointsMap B S hS X' g p = x →
        p ∈ Set.range (pointsMap B S hS O.toFunctor O.ι) := by
  classical
  have hY' : IsAlgebraicSpace B S hS (yoneda.obj Y') := isAlgebraicSpace_yoneda B S hS Y'
  -- `h` and `h ≫ g` are finite
  have hhfin : IsFinite B S hS h :=
    isFinite_of_presheaf_isFiniteLocallyFree B S hS hY' hX' h hhflf
  have hc : IsFinite B S hS (h ≫ g) := isFinite_comp B S hS hhfin hg
  -- `Y'` is separated and locally Noetherian
  have hYsep : ((BigFppfOver.toScheme B S hS).obj Y').IsSeparated :=
    isSeparated_toScheme_obj_of_isSeparated B S hS B.contains_terminal Y' hsep (h ≫ g)
      (isSeparated_of_isFinite B S hS (h ≫ g) hY' hX hc)
  have hYnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Y') :=
    (exists_atlas_iff_of_representable B S hS (yoneda.obj Y')
      (fun T : Scheme.{u} => IsLocallyNoetherian T) Y' (Iso.refl _)).1
      (isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hY' hX (h ≫ g)
        (isLocallyOfFiniteType_of_isFinite B S hS hY' hX hc) hnoeth)
  -- the points of `Y'` over `x` lie in one affine open `A`
  set F := pointsMap B S hS _ (h ≫ g) ⁻¹' {x} with hFdef
  have hF : F.Finite := finite_preimage_singleton_of_isFinite B S hS hY' hX (h ≫ g) hc x
  have : Finite F := hF.to_subtype
  obtain ⟨A, hAaff, hFA⟩ :=
    exists_isAffineOpen_containing_of_stalk_krullDimLE_one_of_finite_components
      ((BigFppfOver.toScheme B S hS).obj Y')
      (finite_irreducibleComponents_of_isCompact ((BigFppfOver.toScheme B S hS).obj Y'))
      (fun y : F => pointsToScheme B S hS Y' y.1) (fun _ => inferInstance)
      (fun y => krullDimLE_one_stalk_of_localRingDimension_le_one B S hS hX Y' (h ≫ g) hc x
        hdim y.1 y.2)
  -- the open `O`: the complement of the image of the points outside `A`
  set C := pointsToScheme B S hS Y' ⁻¹' (A : Set ((BigFppfOver.toScheme B S hS).obj Y'))ᶜ
  have hCcl : IsClosed C :=
    A.isOpen.isClosed_compl.preimage (schemePointsHomeomorph B S hS Y').continuous
  have hOopen : IsOpen (pointsMap B S hS _ h '' C)ᶜ :=
    (isClosed_of_universallyClosed B S hS hX' h
      ((isFinite_iff_isAffineHom_and_isProper B S hS hY' hX' h).mp hhfin).2.universallyClosed
      C hCcl).isOpen_compl
  obtain ⟨O, hO, hOrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hX' _ hOopen
  refine ⟨O, hO, isRepresentable_of_isOpenSubspace_of_image_subset_isAffineOpen B S hS hX' Y' h
    hhsurj hhflf O hO A hAaff ?_, ?_⟩
  · rw [hOrange]
    rintro _ ⟨y, hy, rfl⟩
    by_contra hyA
    exact hy ⟨y, hyA, rfl⟩
  · intro p hp
    rw [hOrange]
    rintro ⟨y, hyC, rfl⟩
    refine hyC (hFA ⟨y, ?_⟩)
    rw [hFdef, Set.mem_preimage, pointsMap_comp_apply, hp]
    rfl

end AlgebraicGeometry.Space

end
