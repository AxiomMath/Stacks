module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Comorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Functoriality
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.Uniqueness
public import StacksCore.Tactic.StacksAttribute

/-!
# Relative differentials on open subschemes

Let `f : X ⟶ S` be a morphism of schemes and let `U ⊆ X`, `V ⊆ S` be open subschemes with
`f(U) ⊆ V`. Restricting the sheaf of relative differentials of `f` to `U` gives the sheaf of
relative differentials of the restricted morphism `U ⟶ V`, by a unique isomorphism compatible
with the universal derivations.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.restrictUniversalDerivation` is the universal relative
  derivation of `f`, read as a relative derivation of `𝒪_U` over `(f|_U)⁻¹ 𝒪_V` with values in
  the restriction of `Ω_{X/S}` to `U`.
* `AlgebraicGeometry.Scheme.Hom.restrictToResLE` is the canonical morphism
  `Ω_{X/S}|_U ⟶ Ω_{U/V}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.restrictToResLE_d`: the canonical morphism carries the
  restricted universal derivation to the universal derivation of `U ⟶ V`.
* `AlgebraicGeometry.Scheme.Hom.restrict_hom_ext`: morphisms out of `Ω_{X/S}|_U` which agree
  on the restricted universal derivation are equal.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentials_restrict` is Tag 01US: the unique
  isomorphism `Ω_{X/S}|_U ≅ Ω_{U/V}` carrying the restricted universal derivation to the
  universal derivation.

## Implementation notes

The sections of the restriction of a module along an open immersion are, by Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, definitionally the sections of the module
over the image, and the comparison `Scheme.Modules.restrictAppIso` is the identity. So the
universal derivation of `f` already *is* a derivation of `𝒪_U` with values in `Ω_{X/S}|_U`;
what has to be proved is its vanishing condition over `(f|_U)⁻¹ 𝒪_V`, and that is supplied by
`AlgebraicGeometry.SheafOfModules.ofComorphism` together with the compatibility
`Scheme.Hom.resLE_appLE` of `appLE` with restriction of a morphism to open subschemes.

Both halves of the isomorphism come from a universal property, so no local computation with
inverse image sheaves is needed. The morphism `Ω_{X/S}|_U ⟶ Ω_{U/V}` is the comparison map of
Tag 01UV for the square with horizontal edges `U.ι` and `V.ι`, read through
`Scheme.Modules.restrictFunctorIsoPullback`; the morphism back is the one induced by the
universal property of `Ω_{U/V}`. One composite is the identity by the universal property of
`Ω_{U/V}`, the other by `restrict_hom_ext`, which is the universal property of `Ω_{X/S}`
transported across the adjunction `restrict ⊣ pushforward`.

## References

* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} {V : S.Opens}

/-- The universal relative derivation of `f : X ⟶ S`, read as a relative derivation of `𝒪_U`
with values in the restriction of `Ω_{X/S}` to an open subscheme `U`. The vanishing condition
recorded here is only the Leibniz rule, over the constant presheaf of rings `ℤ`; the vanishing
condition over `(f|_U)⁻¹ 𝒪_V` is `restrictUniversalDerivation`. -/
noncomputable def restrictDerivationData :
    ((f.relativeDifferentials).restrict U.ι).val.Derivation'
      (SheafOfModules.constIntMap U.toScheme.presheaf) where
  d {W} := (f.universalRelativeDerivation.d).comp
    ((U.ι.appIso W.unop).inv.hom.toAddMonoidHom)
  d_mul {W} a b :=
    Eq.trans (congrArg f.universalRelativeDerivation.d
      (map_mul (U.ι.appIso W.unop).inv.hom a b))
      (f.universalRelativeDerivation.d_mul _ _)
  d_map {W W'} i x :=
    Eq.trans (congrArg f.universalRelativeDerivation.d
      (congrArg (fun g : CommRingCat.Hom _ _ => g.hom x) (U.ι.appIso_inv_naturality i)))
      (f.universalRelativeDerivation.d_map (U.ι.opensFunctor.op.map i) _)
  d_app {W} a := by
    refine SheafOfModules.constIntMap_app_eq_zero _ ?_ a
    change f.universalRelativeDerivation.d ((U.ι.appIso W.unop).inv.hom 1) = 0
    rw [map_one]
    exact f.universalRelativeDerivation.d_one _

/-- The universal relative derivation of `f : X ⟶ S`, read as a relative derivation of `𝒪_U`
over `(f|_U)⁻¹ 𝒪_V` with values in the restriction of `Ω_{X/S}` to `U`. -/
noncomputable def restrictUniversalDerivation (e : U ≤ f ⁻¹ᵁ V) :
    SheafOfModules.SheafDerivation (inverseImageStructureMap (f.resLE V U e))
      ((f.relativeDifferentials).restrict U.ι) :=
  SheafOfModules.ofComorphism _ (restrictDerivationData f) (by
    intro O b
    have hle : U.ι ''ᵁ ((f.resLE V U e) ⁻¹ᵁ O) ≤ f ⁻¹ᵁ (V.ι ''ᵁ O) :=
      (Scheme.Hom.le_resLE_preimage_iff f e O _).mp le_rfl
    have hsec : (U.ι.appIso ((f.resLE V U e) ⁻¹ᵁ O)).inv.hom
          (((f.resLE V U e).app O).hom b) =
        (X.presheaf.map (homOfLE hle).op).hom ((f.app (V.ι ''ᵁ O)).hom b) := by
      rw [Scheme.Opens.ι_appIso, Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]
      rfl
    change f.universalRelativeDerivation.d
      ((U.ι.appIso ((f.resLE V U e) ⁻¹ᵁ O)).inv.hom (((f.resLE V U e).app O).hom b)) = 0
    rw [hsec]
    exact (f.universalRelativeDerivation.d_map (homOfLE hle).op
        ((f.app (V.ι ''ᵁ O)).hom b)).trans
      ((congrArg (fun z => (ConcreteCategory.hom
            ((f.relativeDifferentials).val.map (homOfLE hle).op)) z)
          (SheafOfModules.d_comorphism_eq_zero f f.universalRelativeDerivation
            (V.ι ''ᵁ O) b)).trans
        (map_zero _)))

/-- Two morphisms out of the restriction of `Ω_{X/S}` to an open subscheme `U` which agree on
the restricted universal derivation are equal. This is the universal property of `Ω_{X/S}`,
transported across the adjunction between restriction and pushforward along `U.ι`. -/
theorem restrict_hom_ext {N : U.toScheme.Modules}
    {g₁ g₂ : (f.relativeDifferentials).restrict U.ι ⟶ N}
    (h : ∀ (W : U.toScheme.Opens) (x : Γ(U.toScheme, W)),
      (g₁.val.app (op W)).hom
          ((Scheme.Modules.restrictAppIso U.ι (f.relativeDifferentials) W).inv.hom
            (f.universalRelativeDerivation.d ((U.ι.appIso W).inv.hom x))) =
        (g₂.val.app (op W)).hom
          ((Scheme.Modules.restrictAppIso U.ι (f.relativeDifferentials) W).inv.hom
            (f.universalRelativeDerivation.d ((U.ι.appIso W).inv.hom x)))) :
    g₁ = g₂ := by
  apply ((Scheme.Modules.restrictAdjunction U.ι).homEquiv _ N).injective
  refine (SheafOfModules.universalDerivation_isUniversal
    (inverseImageStructureMap f)).hom_ext ?_
  ext W s
  have key (g : (f.relativeDifferentials).restrict U.ι ⟶ N) :
      (PresheafOfModules.Derivation.postcomp
          (SheafOfModules.universalDerivation (inverseImageStructureMap f))
          (((Scheme.Modules.restrictAdjunction U.ι).homEquiv _ N) g).val).d s =
        (g.val.app (op (U.ι ⁻¹ᵁ W.unop))).hom (f.universalRelativeDerivation.d
          ((U.ι.appIso (U.ι ⁻¹ᵁ W.unop)).inv.hom ((U.ι.app W.unop).hom s))) := by
    rw [Adjunction.homEquiv_unit]
    have hsec : (X.presheaf.map (homOfLE (U.ι.image_preimage_le W.unop)).op).hom s =
        (U.ι.appIso (U.ι ⁻¹ᵁ W.unop)).inv.hom ((U.ι.app W.unop).hom s) :=
      (ConcreteCategory.congr_hom (U.ι.app_appIso_inv W.unop) s).symm
    exact (congrArg (fun z => (ModuleCat.Hom.hom (g.val.app (op (U.ι ⁻¹ᵁ W.unop)))) z)
      ((congrArg f.universalRelativeDerivation.d hsec.symm).trans
        (f.universalRelativeDerivation.d_map
          (homOfLE (U.ι.image_preimage_le W.unop)).op s))).symm
  rw [key g₁, key g₂]
  exact h _ _

/-- Transposing a morphism out of the restriction of a module along an open immersion across
the adjunction between restriction and pushforward is computed on sections by the comparison
of restriction with the inverse image. -/
private lemma restrict_pullback_adjunction_section {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (M : Y.Modules) {N : X.Modules}
    (j : (Scheme.Modules.pullback g).obj M ⟶ N) (W : X.Opens) (s : Γ(M, g ''ᵁ W)) :
    (N.presheaf.map (eqToHom (g.preimage_image_eq W)).op).hom
      ((((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M ≫ j).val.app (.op W)).hom
        ((M.restrictAppIso g W).inv.hom s)) =
      ((((Scheme.Modules.restrictAdjunction g).unit.app M ≫
          (Scheme.Modules.pushforward g).map
            ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M ≫ j)).val.app
          (.op (g ''ᵁ W))).hom s) := by
  let c := (Scheme.Modules.restrictFunctorIsoPullback g).hom.app M ≫ j
  have hn := congrArg (fun q => q.hom ((M.restrictAppIso g W).inv.hom s))
    (c.val.naturality (eqToHom (g.preimage_image_eq W)).op)
  have hunit :
      ((M.restrict g).presheaf.map (eqToHom (g.preimage_image_eq W)).op).hom
          ((M.restrictAppIso g W).inv.hom s) =
        (((Scheme.Modules.restrictAdjunction g).unit.app M).app (g ''ᵁ W)).hom s := by
    show (M.presheaf.map (g.opensFunctor.map (eqToHom (g.preimage_image_eq W))).op).hom s =
      (M.presheaf.map (homOfLE (g.image_preimage_le (g ''ᵁ W))).op).hom s
    rw [Subsingleton.elim (g.opensFunctor.map (eqToHom (g.preimage_image_eq W)))
      (homOfLE (g.image_preimage_le (g ''ᵁ W)))]
  show (N.val.map (eqToHom (g.preimage_image_eq W)).op).hom
      ((c.val.app (.op W)).hom ((M.restrictAppIso g W).inv.hom s)) =
    (c.val.app (.op (g ⁻¹ᵁ g ''ᵁ W))).hom
      ((((Scheme.Modules.restrictAdjunction g).unit.app M).app (g ''ᵁ W)).hom s)
  exact hn.symm.trans (congrArg (c.val.app (.op (g ⁻¹ᵁ g ''ᵁ W))).hom hunit)

/-- For an open immersion, the unit of the adjunction between inverse image and pushforward,
followed by the pushforward of a morphism, factors through the unit of the adjunction between
restriction and pushforward and the comparison of restriction with the inverse image. -/
private theorem pullbackPushforwardAdjunction_unit_comp_map {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (M : Y.Modules) {N : X.Modules}
    (j : (Scheme.Modules.pullback g).obj M ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
        (Scheme.Modules.pushforward g).map j =
      (Scheme.Modules.restrictAdjunction g).unit.app M ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M ≫ j) := by
  calc
    _ = ((Scheme.Modules.restrictAdjunction g).unit.app M ≫
          (Scheme.Modules.pushforward g).map
            (((Scheme.Modules.restrictAdjunction g).leftAdjointUniq
              (Scheme.Modules.pullbackPushforwardAdjunction g)).hom.app M)) ≫
          (Scheme.Modules.pushforward g).map j := by
        rw [← Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction g)
          (Scheme.Modules.pullbackPushforwardAdjunction g) M]
    _ = ((Scheme.Modules.restrictAdjunction g).unit.app M ≫
          (Scheme.Modules.pushforward g).map
            ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M)) ≫
          (Scheme.Modules.pushforward g).map j := rfl
    _ = _ := by rw [Category.assoc, ← Functor.map_comp]

/-- The canonical morphism `Ω_{X/S}|_U ⟶ Ω_{U/V}`: the comparison map of Tag 01UV for the
square with horizontal edges the two open immersions, read through the comparison of
restriction with the inverse image. -/
noncomputable def restrictToResLE (e : U ≤ f ⁻¹ᵁ V) :
    (f.relativeDifferentials).restrict U.ι ⟶ (f.resLE V U e).relativeDifferentials :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app (f.relativeDifferentials) ≫
    relativeDifferentialsMap U.ι f (f.resLE V U e) V.ι (Scheme.Hom.resLE_comp_ι f e).symm

/-- The canonical morphism `Ω_{X/S}|_U ⟶ Ω_{U/V}` carries the restricted universal derivation
to the universal derivation of the restricted morphism. -/
theorem restrictToResLE_d (e : U ≤ f ⁻¹ᵁ V) (W : U.toScheme.Opens) (x : Γ(U.toScheme, W)) :
    ((restrictToResLE f e).val.app (.op W)).hom
        ((Scheme.Modules.restrictAppIso U.ι (f.relativeDifferentials) W).inv.hom
          (f.universalRelativeDerivation.d ((U.ι.appIso W).inv.hom x))) =
      (f.resLE V U e).universalRelativeDerivation.d x := by
  set Ω := f.relativeDifferentials
  set Ω' := (f.resLE V U e).relativeDifferentials
  set j := relativeDifferentialsMap U.ι f (f.resLE V U e) V.ι
    (Scheme.Hom.resLE_comp_ι f e).symm
  have hdiff : IsRelativeDifferentialsMap U.ι f (f.resLE V U e) j :=
    (isRelativeDifferentialsMap_iff_eq U.ι f (f.resLE V U e) V.ι
      (Scheme.Hom.resLE_comp_ι f e).symm j).mpr rfl
  have h := hdiff (U.ι ''ᵁ W) (((U.ι.appIso W).inv).hom x)
  set hsec := f.universalRelativeDerivation.d (((U.ι.appIso W).inv).hom x)
  have heq := congrArg (fun q => (q.val.app (.op (U.ι ''ᵁ W))).hom hsec)
    ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).homEquiv_apply Ω Ω' j)
  have hcompApp := congrArg (fun q => (q.val.app (.op (U.ι ''ᵁ W))).hom hsec)
    (pullbackPushforwardAdjunction_unit_comp_map U.ι Ω j)
  have hsource :
      (Ω'.presheaf.map (eqToHom (U.ι.preimage_image_eq W)).op).hom
        (((restrictToResLE f e).val.app (.op W)).hom
          (((Scheme.Modules.restrictAppIso U.ι Ω W).inv).hom hsec)) =
        (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).homEquiv Ω Ω' j).val.app
          (.op (U.ι ''ᵁ W))).hom hsec := by
    rw [heq]
    have hb := restrict_pullback_adjunction_section U.ι Ω j W hsec
    simpa [restrictToResLE, Scheme.Modules.Hom.comp_app] using hb.trans hcompApp.symm
  set d' := (f.resLE V U e).universalRelativeDerivation
  have htarget :
      (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).homEquiv Ω Ω' j).val.app
          (.op (U.ι ''ᵁ W))).hom hsec =
        (Ω'.presheaf.map (eqToHom (U.ι.preimage_image_eq W)).op).hom (d'.d x) := by
    have happ :
        (U.ι.app (U.ι ''ᵁ W)).hom ((U.ι.appIso W).inv.hom x) =
          (U.toScheme.presheaf.map (eqToHom (U.ι.preimage_image_eq W)).op).hom x := by
      show ((U.ι.appIso W).inv ≫ U.ι.app (U.ι ''ᵁ W)).hom x = _
      rw [Scheme.Hom.appIso_inv_app]
    rw [happ] at h
    change _ = d'.d
      ((ConcreteCategory.hom
        (((sheafToPresheaf (Opens.grothendieckTopology U.toScheme) CommRingCat).obj
          U.toScheme.sheaf).map (eqToHom (U.ι.preimage_image_eq W)).op)) x) at h
    rwa [d'.d_map (eqToHom (U.ι.preimage_image_eq W)).op x] at h
  exact (ConcreteCategory.bijective_of_isIso
    (Ω'.presheaf.map (eqToHom (U.ι.preimage_image_eq W)).op)).1 (hsource.trans htarget)

/-- Compatibility with the universal derivations, stated on sections as in Tag 01US, is the
statement that postcomposition carries the restricted universal derivation to the universal
derivation of the restricted morphism. -/
theorem postcomp_restrict_eq_iff (e : U ≤ f ⁻¹ᵁ V)
    (g : (f.relativeDifferentials).restrict U.ι ⟶ (f.resLE V U e).relativeDifferentials) :
    (restrictUniversalDerivation f e).postcomp g.val =
        (f.resLE V U e).universalRelativeDerivation ↔
      ∀ (W : U.toScheme.Opens) (x : Γ(U.toScheme, W)),
        (g.val.app (.op W)).hom
            ((Scheme.Modules.restrictAppIso U.ι (f.relativeDifferentials) W).inv.hom
              (f.universalRelativeDerivation.d ((U.ι.appIso W).inv.hom x))) =
          (f.resLE V U e).universalRelativeDerivation.d x := by
  refine ⟨fun hg W x => PresheafOfModules.Derivation.congr_d hg x, fun hg => ?_⟩
  ext W x
  exact hg W.unop x

/-- The restricted universal derivation is universal: it represents the derivations of `𝒪_U`
over `(f|_U)⁻¹ 𝒪_V`. Existence of the factorization comes from the universal property of
`Ω_{U/V}` through `restrictToResLE`, and uniqueness from `restrict_hom_ext`. -/
theorem restrictUniversalDerivation_isUniversal (e : U ≤ f ⁻¹ᵁ V) :
    SheafOfModules.IsUniversal (restrictUniversalDerivation f e) := by
  have huniv' := SheafOfModules.universalDerivation_isUniversal
    (inverseImageStructureMap (f.resLE V U e))
  have hforward : (restrictUniversalDerivation f e).postcomp (restrictToResLE f e).val =
      (f.resLE V U e).universalRelativeDerivation :=
    (postcomp_restrict_eq_iff f e _).mpr (restrictToResLE_d f e)
  intro F D
  have hex : (restrictUniversalDerivation f e).postcomp
      (restrictToResLE f e ≫ huniv'.desc D).val = D :=
    ((SheafOfModules.postcomp_comp_val (restrictUniversalDerivation f e)
        (restrictToResLE f e) (huniv'.desc D)).symm.trans
      (congrArg (fun E : SheafOfModules.SheafDerivation
          (inverseImageStructureMap (f.resLE V U e))
          ((f.resLE V U e).relativeDifferentials) =>
        E.postcomp (huniv'.desc D).val) hforward)).trans (huniv'.postcomp_desc D)
  exact ⟨restrictToResLE f e ≫ huniv'.desc D, hex, fun g hg => restrict_hom_ext f fun W x =>
    (PresheafOfModules.Derivation.congr_d hg x).trans
      (PresheafOfModules.Derivation.congr_d hex x).symm⟩

/-- **Stacks Project, Tag 01US.** Let `f : X ⟶ S` be a morphism of schemes and let `U ⊆ X`,
`V ⊆ S` be open subschemes with `f(U) ⊆ V`. There is a unique isomorphism
`Ω_{X/S}|_U ≅ Ω_{U/V}` of `𝒪_U`-modules carrying the restriction of the universal derivation
of `f` to the universal derivation of the restricted morphism. -/
theorem relativeDifferentials_restrict (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) :
    ∃! i : (f.relativeDifferentials).restrict U.ι ≅ (f.resLE V U e).relativeDifferentials,
      ∀ (W : U.toScheme.Opens) (x : Γ(U.toScheme, W)),
        (i.hom.val.app (.op W)).hom
            ((Scheme.Modules.restrictAppIso U.ι (f.relativeDifferentials) W).inv.hom
              (f.universalRelativeDerivation.d ((U.ι.appIso W).inv.hom x))) =
          (f.resLE V U e).universalRelativeDerivation.d x := by
  have hR := restrictUniversalDerivation_isUniversal f e
  have huniv' := SheafOfModules.universalDerivation_isUniversal
    (inverseImageStructureMap (f.resLE V U e))
  exact ⟨hR.uniqueIso huniv', (postcomp_restrict_eq_iff f e _).mp
    (hR.uniqueIso_compatible huniv'),
    fun k hk => hR.eq_uniqueIso huniv' k ((postcomp_restrict_eq_iff f e _).mpr hk)⟩

end AlgebraicGeometry.Scheme.Hom
