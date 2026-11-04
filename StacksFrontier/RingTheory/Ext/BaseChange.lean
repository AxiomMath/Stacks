module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import StacksFrontier.RingTheory.Tor.TorOneBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change for Ext

Fix a flat ring homomorphism `φ : R → R'` of commutative rings, let `M` be an `R`-module and
`N'` an `R'`-module. For every `i ≥ 0` there is a natural comparison map
  `c^i : Ext^i_{R'}(M ⊗_R R', N') → Ext^i_R(M, N')`,
where on the right `N'` is viewed as an `R`-module by restriction of scalars along `φ`. The
theorem (Stacks tag 087N) is that `c^i` is an isomorphism of abelian groups for every
`i ≥ 0`.

Restriction of scalars is `ModuleCat.restrictScalars f : ModuleCat R' ⥤ ModuleCat R` and
extension of scalars is `ModuleCat.extendScalars f : ModuleCat R ⥤ ModuleCat R'`, left
adjoint to it; the adjunction (Stacks 05DQ) is `ModuleCat.extendRestrictScalarsAdj`. The Ext
functors are `CategoryTheory.Abelian.Ext X Y i`, the derived functors of Hom, defined for any
abelian category with `HasExt`; `ModuleCat.{0} R` has `HasExt.{0}` as an instance. The
comparison map `c^i` is induced by the adjunction, and in degree `0` it is the adjunction
isomorphism `Hom_{R'}(M ⊗_R R', N') ≅ Hom_R(M, N')`. Note that `restrictScalars f` is exact,
being both a left and a right adjoint, hence acts on `Ext` via `Functor.mapExtAddHom`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian

/-- The functor `ModuleCat.restrictScalars f` preserves finite colimits, being a left adjoint
to `coextendScalars f`. -/
@[ega "III 7.1.3" "partial", sga "4 IV 11.1.6" "special case"]
instance restrictScalars_preservesFiniteColimits
    {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    Limits.PreservesFiniteColimits (ModuleCat.restrictScalars f) :=
  have : Limits.PreservesColimitsOfSize.{0, 0} (ModuleCat.restrictScalars f) :=
    (ModuleCat.restrictCoextendScalarsAdj f).leftAdjoint_preservesColimits
  Limits.PreservesColimitsOfSize.preservesFiniteColimits _

/-- The natural comparison map `c^i`:
`Ext^i_{R'}(M ⊗_R R', N') → Ext^i_R(M, N')`.

It is the composite of the functorial action of the exact functor
`restrictScalars f` on `Ext`
(`Ext^i_{R'}(M ⊗_R R', N') → Ext^i_R(restrictScalars (M ⊗_R R'), restrictScalars N')`)
with precomposition by the degree-0 class of the unit of the
extension/restriction adjunction
`η_M : M ⟶ restrictScalars (M ⊗_R R')`.
In degree `i = 0` this reduces to the adjunction isomorphism
`Hom_{R'}(M ⊗_R R', N') ≅ Hom_R(M, N')`. -/
noncomputable def extFlatBaseChangeComparison {R R' : Type} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{0} R) (N' : ModuleCat.{0} R') (i : ℕ) :
    Ext.{0} ((ModuleCat.extendScalars f).obj M) N' i →+
      Ext.{0} M ((ModuleCat.restrictScalars f).obj N') i :=
  ((Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj f).unit.app M)).precomp
      ((ModuleCat.restrictScalars f).obj N') (zero_add i)).comp
    ((ModuleCat.restrictScalars f).mapExtAddHom ((ModuleCat.extendScalars f).obj M) N' i)

/-- **Extension of scalars along a flat ring map preserves finite limits.** -/
@[sga "3 VIIB 3.3.3" "Clause"]
theorem extendScalars_preservesFiniteLimits_of_flat {R R' : Type} [CommRing R] [CommRing R']
    {f : R →+* R'} (hf : f.Flat) :
    Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{0,0,0} f) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf

/-- **`extendScalars f` preserves finite colimits**, being a left adjoint to
`restrictScalars f`. -/
@[ega "0 4.3.2" "special case"]
theorem extendScalars_preservesFiniteColimits {R R' : Type} [CommRing R] [CommRing R']
    (f : R →+* R') :
    Limits.PreservesFiniteColimits (ModuleCat.extendScalars.{0,0,0} f) :=
  have : Limits.PreservesColimitsOfSize.{0,0} (ModuleCat.extendScalars.{0,0,0} f) :=
    (ModuleCat.extendRestrictScalarsAdj f).leftAdjoint_preservesColimits
  Limits.PreservesColimitsOfSize.preservesFiniteColimits _

/-- **Extension of scalars along a flat ring map is additive.** -/
theorem extendScalars_additive_of_flat {R R' : Type} [CommRing R] [CommRing R']
    {f : R →+* R'} (hf : f.Flat) :
    (ModuleCat.extendScalars.{0,0,0} f).Additive := by
  have h1 : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{0,0,0} f) :=
    extendScalars_preservesFiniteLimits_of_flat hf
  have hbp : Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair)
      (ModuleCat.extendScalars.{0,0,0} f) := h1.preservesFiniteLimits _
  have h2 : Limits.PreservesColimitsOfSize.{0,0} (ModuleCat.extendScalars.{0,0,0} f) :=
    (ModuleCat.extendRestrictScalarsAdj f).leftAdjoint_preservesColimits
  exact Functor.additive_of_preserves_binary_products (ModuleCat.extendScalars.{0,0,0} f)

/-- **`extendScalars f` preserves projective objects**, being left adjoint to
`restrictScalars f`, which preserves epimorphisms. -/
@[ega "0 19.2.5" "(ii), special case", ega "III 6.3.8" "Projectivity clause"]
theorem extendScalars_preservesProjectiveObjects {R R' : Type} [CommRing R] [CommRing R']
    (f : R →+* R') :
    (ModuleCat.extendScalars.{0,0,0} f).PreservesProjectiveObjects := by
  have : (ModuleCat.restrictScalars f).PreservesEpimorphisms := inferInstance
  exact Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (ModuleCat.extendRestrictScalarsAdj f)

/-- **The comparison map is bijective in degree `0`.** Under `Ext.homEquiv₀`, the map
`extFlatBaseChangeComparison f M N' 0` is the adjunction bijection
`(ModuleCat.extendRestrictScalarsAdj f).homEquiv M N'`. -/
theorem flat_base_change_ext_zero {R R' : Type} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{0} R) (N' : ModuleCat.{0} R') :
    Function.Bijective (extFlatBaseChangeComparison f M N' 0) := by
  have key : ⇑(extFlatBaseChangeComparison f M N' 0)
      = ⇑Ext.homEquiv₀.symm ∘ ⇑((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N')
          ∘ ⇑Ext.homEquiv₀ := by
    funext x
    obtain ⟨g, rfl⟩ := Ext.homEquiv₀.symm.surjective x
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    have hinner : (ModuleCat.restrictScalars f).mapExtAddHom
          ((ModuleCat.extendScalars f).obj M) N' 0 (Ext.homEquiv₀.symm g)
        = Ext.mk₀ ((ModuleCat.restrictScalars f).map g) := by
      rw [Functor.mapExtAddHom_apply, Ext.homEquiv₀_symm_apply, Ext.mapExactFunctor_mk₀]
    have hrhs : Ext.homEquiv₀.symm ((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N' g)
        = (Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj f).unit.app M)).precomp
            ((ModuleCat.restrictScalars f).obj N') (zero_add 0)
            (Ext.mk₀ ((ModuleCat.restrictScalars f).map g)) := by
      rw [Adjunction.homEquiv_apply, Ext.homEquiv₀_symm_apply, ← Ext.mk₀_comp_mk₀]; rfl
    rw [hrhs]
    show (Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj f).unit.app M)).precomp
        ((ModuleCat.restrictScalars f).obj N') (zero_add 0)
        ((ModuleCat.restrictScalars f).mapExtAddHom
          ((ModuleCat.extendScalars f).obj M) N' 0 (Ext.homEquiv₀.symm g)) = _
    rw [hinner]
  rw [key]
  exact Ext.homEquiv₀.symm.bijective.comp
    (((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N').bijective.comp
      Ext.homEquiv₀.bijective)

/-- The comparison map is `Ext.mapExactFunctor` followed by composition with the unit class. -/
private theorem comparison_apply_eq_comp {R R' : Type} [CommRing R] [CommRing R']
    (f : R →+* R') (M : ModuleCat.{0} R) (N' : ModuleCat.{0} R') (k : ℕ)
    (y : Ext.{0} ((ModuleCat.extendScalars f).obj M) N' k) :
    extFlatBaseChangeComparison f M N' k y
      = (Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj f).unit.app M)).comp
          (Ext.mapExactFunctor (ModuleCat.restrictScalars f) y) (zero_add k) := by
  rw [extFlatBaseChangeComparison]
  show ((Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj f).unit.app M)).precomp
      ((ModuleCat.restrictScalars f).obj N') (zero_add k))
      ((ModuleCat.restrictScalars f).mapExtAddHom
        ((ModuleCat.extendScalars f).obj M) N' k y) = _
  rw [Ext.precomp, Ext.bilinearComp_apply_apply, Functor.mapExtAddHom_apply]

/-- **Naturality of the comparison map in `M`.** For a morphism `u : M₁ ⟶ M₂` in
`ModuleCat R`, precomposition with the class of `u` after `c^i_{M₂}` equals `c^i_{M₁}` after
precomposition with the class of `(extendScalars f).map u`. -/
theorem extFlatBaseChangeComparison_naturality_mor {R R' : Type} [CommRing R] [CommRing R']
    (f : R →+* R') {M₁ M₂ : ModuleCat.{0} R} (u : M₁ ⟶ M₂)
    (N' : ModuleCat.{0} R') (i : ℕ) (x : Ext.{0} ((ModuleCat.extendScalars f).obj M₂) N' i) :
    (Ext.mk₀ u).precomp ((ModuleCat.restrictScalars f).obj N') (zero_add i)
        (extFlatBaseChangeComparison f M₂ N' i x)
      = extFlatBaseChangeComparison f M₁ N' i
          ((Ext.mk₀ ((ModuleCat.extendScalars f).map u)).precomp N' (zero_add i) x) := by
  have hnat := (ModuleCat.extendRestrictScalarsAdj f).unit.naturality u
  simp only [Functor.comp_map, Functor.id_obj, Functor.id_map] at hnat
  rw [comparison_apply_eq_comp, comparison_apply_eq_comp, Ext.bilinearComp_apply_apply,
    Ext.bilinearComp_apply_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc (Ext.mk₀ u) _ _ (zero_add 0) (zero_add i) (by omega),
    ← Ext.comp_assoc (Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj f).unit.app M₁)) _ _
      (zero_add 0) (zero_add i) (by omega), Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, hnat]

/-- **Compatibility of the comparison map with connecting maps.** Let
`S : 0 → K → P → M → 0` be short exact in `ModuleCat R` such that its image `L S` under
`L = extendScalars f` is short exact. Then for `x : Ext (L K) N' i` and `hi : 1 + i = j`,
```
c^j_M ((L S).extClass.comp x hi) = S.extClass.comp (c^i_K x) hi.
```
-/
theorem extFlatBaseChangeComparison_naturality_delta {R R' : Type} [CommRing R] [CommRing R']
    (f : R →+* R') (S : ShortComplex (ModuleCat.{0} R)) (hS : S.ShortExact)
    (hLS : (S.map (ModuleCat.extendScalars f)).ShortExact)
    (N' : ModuleCat.{0} R') (i j : ℕ) (hi : 1 + i = j)
    (x : Ext.{0} ((ModuleCat.extendScalars f).obj S.X₁) N' i) :
    extFlatBaseChangeComparison f S.X₃ N' j (hLS.extClass.comp x hi)
      = hS.extClass.comp (extFlatBaseChangeComparison f S.X₁ N' i x) hi := by
  rw [comparison_apply_eq_comp, comparison_apply_eq_comp, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  set η := (ModuleCat.extendRestrictScalarsAdj f).unit
  rw [← Ext.comp_assoc (Ext.mk₀ (η.app S.X₃))
      ((ShortComplex.ShortExact.map_of_exact hLS (ModuleCat.restrictScalars f)).extClass)
      (Ext.mapExactFunctor (ModuleCat.restrictScalars f) x)
      (zero_add 1) hi (by omega),
    ← Ext.comp_assoc hS.extClass (Ext.mk₀ (η.app S.X₁))
      (Ext.mapExactFunctor (ModuleCat.restrictScalars f) x)
      (add_zero 1) (zero_add i) (by omega)]
  congr 1
  exact (hS.extClass_naturality
    (ShortComplex.ShortExact.map_of_exact hLS (ModuleCat.restrictScalars f))
    (S.mapNatTrans η)).symm

/-- **Flat base change for Ext.**
For a flat ring map `f : R → R'`, an `R`-module `M`, an `R'`-module `N'`, and
each `i ≥ 0`, the comparison map `c^i` of `extFlatBaseChangeComparison` is an
isomorphism of abelian groups (here phrased as bijectivity of the underlying
group homomorphism). -/
@[stacks 087N]
theorem flat_base_change_ext {R R' : Type} [CommRing R] [CommRing R']
    (f : R →+* R') (hf : f.Flat) (M : ModuleCat.{0} R) (N' : ModuleCat.{0} R') (i : ℕ) :
    Function.Bijective (extFlatBaseChangeComparison f M N' i) := by
  induction i generalizing M with
  | zero => exact flat_base_change_ext_zero f M N'
  | succ n ih =>
    have hlim : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{0,0,0} f) :=
      extendScalars_preservesFiniteLimits_of_flat hf
    have hcolim : Limits.PreservesFiniteColimits (ModuleCat.extendScalars.{0,0,0} f) :=
      extendScalars_preservesFiniteColimits f
    have hadd : (ModuleCat.extendScalars.{0,0,0} f).Additive :=
      extendScalars_additive_of_flat hf
    have hproj : (ModuleCat.extendScalars.{0,0,0} f).PreservesProjectiveObjects :=
      extendScalars_preservesProjectiveObjects f
    set S := M.projectiveShortComplex
    have hS : S.ShortExact := M.shortExact_projectiveShortComplex
    have hPproj : Projective S.X₂ := inferInstance
    have hLS : (S.map (ModuleCat.extendScalars f)).ShortExact := hS.map_of_exact _
    have hLPproj : Projective (S.map (ModuleCat.extendScalars f)).X₂ :=
      (ModuleCat.extendScalars f).projective_obj_of_projective hPproj
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (extFlatBaseChangeComparison f S.X₂ N' n) (extFlatBaseChangeComparison f S.X₁ N' n)
      (extFlatBaseChangeComparison f S.X₃ N' (n + 1))
      ?hc₁ ?hc₂
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.contravariant_sequence_exact₁' hLS N' n (n + 1) (add_comm 1 n)))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.contravariant_sequence_exact₁' hS ((ModuleCat.restrictScalars f).obj N')
          n (n + 1) (add_comm 1 n)))
      (ih _).surjective (ih _)
      ?hf₂ ?hg₂
    case hc₁ =>
      ext x
      exact extFlatBaseChangeComparison_naturality_mor f S.f N' n x
    case hc₂ =>
      ext x
      exact (extFlatBaseChangeComparison_naturality_delta f S hS hLS N' n (n + 1)
        (add_comm 1 n) x).symm
    case hf₂ =>
      exact fun x₃ ↦ Ext.contravariant_sequence_exact₃ hLS _ x₃
        (Ext.eq_zero_of_projective _) (add_comm 1 n)
    case hg₂ =>
      exact fun y₃ ↦ Ext.contravariant_sequence_exact₃ hS _ y₃
        (Ext.eq_zero_of_projective _) (add_comm 1 n)
