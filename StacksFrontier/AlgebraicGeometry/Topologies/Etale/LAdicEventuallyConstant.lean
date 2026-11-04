module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ConstructibleExtendScalars
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LAdicSheaves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Eventually constant reductions of constructible sheaves

An inverse system of constructible sheaves of modules over the successive quotients of `ℤ_ℓ`
determines an ℓ-adic sheaf when each fixed finite reduction is eventually constant.

## Main definitions

* `AlgebraicGeometry.SmallEtale.FiniteLevelSheaf.reduceTo`: reduction from level `n` to any
  earlier level `k`.
* `AlgebraicGeometry.SmallEtale.FiniteLevelSheaf.canonicalReductionComparison`: the canonical
  comparison between iterated and direct reduction.
* `AlgebraicGeometry.SmallEtale.FiniteLevelSheaf.canonicalReductionTransition`: its adjoint
  quotient map.
* `AlgebraicGeometry.SmallEtale.FiniteLevelSheaf.canonicalRestrictionComparison`: the
  identification of reduction after restricting coefficients with direct reduction.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_lAdicSheaf_of_eventuallyConstant_reductions`: the ℓ-adic
  sheaf built from the eventually constant reductions.

## Implementation notes

Levels are indexed from zero, so level `n` has coefficients in `ℤ/ℓⁿ⁺¹ℤ`. Quotienting by
`ℓᵏ⁺¹` is sheafified extension of scalars. The eventual-isomorphism hypothesis uses the image of
the transition under this extension-of-scalars functor. Its target is the reduction of the
preceding level after restriction of scalars, canonically the same quotient. The conclusion
identifies all finite levels with the stable values of these quotients, compatibly with both the
original inverse-system maps and the canonical quotient maps between successive reductions.

The construction is the eventually-constant-sequence argument: for each fixed level `k` the
reductions of the levels above it form an inverse sequence which is eventually constant, so it
has a stable value, and that value is the level `k` of the ℓ-adic sheaf. Constructibility of the
stable value is Tag 0GKB. That the comparison maps are isomorphisms past the stabilization index
uses two facts: the eventual-isomorphism hypothesis, and that the comparison between reduction
after restriction of scalars and direct reduction is always an isomorphism, which holds because
the coefficient quotient map is surjective, so restriction of scalars along it is fully
faithful and the counit of the extension/restriction adjunction is invertible.

The module universe is free, inherited from `AlgebraicGeometry.SmallEtale.LAdicSheaf`.

## References

* [Stacks Project, Tag 03UN](https://stacks.math.columbia.edu/tag/03UN)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
  HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.obj X.property)
  (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))]

/-- Reduction of a finite-level module sheaf modulo `ℓ^(k+1)`. -/
public abbrev FiniteLevelSheaf.reduceTo (n k : ℕ) (h : k ≤ n)
    (G : FiniteLevelSheaf.{u, m} B X ℓ n) : FiniteLevelSheaf.{u, m} B X ℓ k :=
  (Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property)
    (ModuleCat.extendScalars.{0, 0, m}
      (ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 1 ≤ n + 1)) _ :
        ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 1))))).obj G

/-- The canonical comparison between iterated and direct scalar reduction. It is induced by
composition of the two coefficient-ring quotient maps. -/
public noncomputable def FiniteLevelSheaf.canonicalReductionComparison
    (n k : ℕ) (h : k + 1 ≤ n) (G : FiniteLevelSheaf.{u, m} B X ℓ n) :
    (FiniteLevelSheaf.reduceTo B X ℓ n (k + 1) h G).scalarReduction B X ℓ k ≅
      FiniteLevelSheaf.reduceTo B X ℓ n k (by omega) G := by
  let f : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 2)) :=
    ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 2 ≤ n + 1)) _
  let g : ZMod (ℓ ^ (k + 2)) →+* ZMod (ℓ ^ (k + 1)) := finiteLevelRingHom ℓ k
  let r : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 1)) :=
    ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 1 ≤ n + 1)) _
  have hr : g.comp f = r := by
    ext x
    simp [f, g, r, finiteLevelRingHom]
  let J := SmallEtale.topology B X.obj X.property
  let P := G.obj ⋙ ModuleCat.extendScalars.{0, 0, m} f
  have : J.PreservesSheafification (ModuleCat.extendScalars.{0, 0, m} g) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.extendRestrictScalarsAdj.{m, 0, 0} g)
  let a := CategoryTheory.presheafToSheafCompComposeAndSheafifyIso J
    (ModuleCat.extendScalars.{0, 0, m} g) |>.app P
  let b := (CategoryTheory.presheafToSheaf J (ModuleCat.{m} (ZMod (ℓ ^ (k + 1))))).mapIso
    (Functor.isoWhiskerLeft G.obj (ModuleCat.extendScalarsComp f g))
  rw [hr] at b
  exact a ≪≫ b.symm

/-- The quotient map from reduction modulo `ℓ^(k+2)` to reduction modulo `ℓ^(k+1)` of the same
finite-level sheaf. -/
public noncomputable def FiniteLevelSheaf.canonicalReductionTransition
    (n k : ℕ) (h : k + 1 ≤ n) (G : FiniteLevelSheaf.{u, m} B X ℓ n) :
    FiniteLevelSheaf.reduceTo B X ℓ n (k + 1) h G ⟶
      (FiniteLevelSheaf.reduceTo B X ℓ n k (by omega) G).restrictScalars B X ℓ k :=
  ((Sheaf.adjunction (SmallEtale.topology B X.obj X.property)
    (ModuleCat.extendRestrictScalarsAdj (finiteLevelRingHom ℓ k))).homEquiv
      (FiniteLevelSheaf.reduceTo B X ℓ n (k + 1) h G)
      (FiniteLevelSheaf.reduceTo B X ℓ n k (by omega) G))
      (FiniteLevelSheaf.canonicalReductionComparison B X ℓ n k h G).hom

/-- The canonical map from reduction of a sheaf after restriction from level `n+1` to level `n`,
to its direct reduction. On a pure tensor it sends `1 ⊗ x` to `1 ⊗ x`. -/
public noncomputable def FiniteLevelSheaf.canonicalRestrictionComparison
    (n k : ℕ) (h : k ≤ n) (G : FiniteLevelSheaf.{u, m} B X ℓ n) :
    (Sheaf.composeAndSheafify
      (SmallEtale.topology B X.obj X.property)
      (ModuleCat.extendScalars.{0, 0, m}
        (ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 1 ≤ n + 2)) _ :
          ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1))))).obj
        (G.restrictScalars B X ℓ n) ⟶
      FiniteLevelSheaf.reduceTo B X ℓ n k h G := by
  let f : ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (n + 1)) := finiteLevelRingHom ℓ n
  let g : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 1)) :=
    ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 1 ≤ n + 1)) _
  let r : ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1)) :=
    ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 1 ≤ n + 2)) _
  have hr : g.comp f = r := by
    ext x
    simp [f, g, r, finiteLevelRingHom]
  let J := SmallEtale.topology B X.obj X.property
  let P := G.obj ⋙ ModuleCat.restrictScalars.{m, 0, 0} f
  have : J.PreservesSheafification (ModuleCat.extendScalars.{0, 0, m} r) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.extendRestrictScalarsAdj.{m, 0, 0} r)
  let a := CategoryTheory.presheafToSheafCompComposeAndSheafifyIso J
    (ModuleCat.extendScalars.{0, 0, m} r) |>.app P
  let τ : P ⋙ ModuleCat.extendScalars.{0, 0, m} r ⟶
      G.obj ⋙ ModuleCat.extendScalars.{0, 0, m} g := by
    rw [← hr]
    exact Functor.whiskerLeft G.obj
      (Functor.whiskerLeft (ModuleCat.restrictScalars f)
        (ModuleCat.extendScalarsComp f g).hom ≫
        Functor.whiskerRight (ModuleCat.extendRestrictScalarsAdj f).counit
          (ModuleCat.extendScalars g))
  let b := ((CategoryTheory.sheafificationAdjunction J
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 2))))).counit.app
      (G.restrictScalars B X ℓ n))
  exact ((Sheaf.composeAndSheafify J
    (ModuleCat.extendScalars.{0, 0, m} r)).mapIso (asIso b).symm).hom ≫
      a.hom ≫ (CategoryTheory.presheafToSheaf J _).map τ

/-- An arithmetic step used repeatedly: a level below `n` is below `n + 1`. -/
private theorem reductionExponent_le (k n : ℕ) (h : k ≤ n) : k + 1 ≤ n + 2 :=
  Nat.le_trans (Nat.add_le_add_right h 1) (Nat.le_succ (n + 1))

section ScalarReductionCompatibility

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
  HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))]

/-- The inverse of the sheafification counit on a sheaf is the unit of sheafification. -/
private lemma counit_inv_hom {C D : Type*} [Category C] [Category D]
    (J : GrothendieckTopology C) [HasWeakSheafify J D] (F : Sheaf J D) :
    (inv ((sheafificationAdjunction J D).counit.app F)).hom = toSheafify J F.obj := by
  apply (cancel_mono (((sheafificationAdjunction J D).counit.app F).hom)).mp
  rw [sheafificationAdjunction_counit_app_val, toSheafify_sheafifyLift J (𝟙 F.obj) F.property]
  have hh := (sheafToPresheaf J D).congr_map
    (IsIso.inv_hom_id ((sheafificationAdjunction J D).counit.app F))
  change (inv ((sheafificationAdjunction J D).counit.app F)).hom ≫
    ((sheafificationAdjunction J D).counit.app F).hom = 𝟙 F.obj at hh
  rw [sheafificationAdjunction_counit_app_val] at hh
  exact hh

/-- Composing the image of the inverse counit with the comparison isomorphism for sheafified
postcomposition is the identity. -/
private lemma cancel_sheaf_comparison {C D E : Type*}
    [Category C] [Category D] [Category E]
    (J : GrothendieckTopology C) [HasWeakSheafify J D] [HasWeakSheafify J E]
    (L : D ⥤ E) [J.PreservesSheafification L] (F : Sheaf J D) :
    (Sheaf.composeAndSheafify J L).map
        (inv ((sheafificationAdjunction J D).counit.app F)) ≫
      (presheafToSheafCompComposeAndSheafifyIso J L).hom.app F.obj = 𝟙 _ := by
  show (presheafToSheaf J E).map (Functor.whiskerRight
    (inv ((sheafificationAdjunction J D).counit.app F)).hom L) ≫ _ = _
  rw [counit_inv_hom, ← presheafToSheafCompComposeAndSheafifyIso_inv_app J L F.obj]
  exact (presheafToSheafCompComposeAndSheafifyIso J L).inv_hom_id_app F.obj

universe w v

/-- The extension/restriction adjunction for a change of coefficient rings, at the module
universe used throughout. -/
private abbrev esAdj {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S) :=
  ModuleCat.extendRestrictScalarsAdj.{max v w, w, w} f

/-- The canonical generator `1 ⊗ x` of an extension of scalars, as the unit of the
extension/restriction adjunction. Stating it this way, rather than with the `⊗ₜ` notation,
keeps the module structure on the target the one carried by `ModuleCat`, which is what makes
the computations below type-check without relaxing transparency. -/
private def esOne {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{max v w} R) (x : M) : (ModuleCat.extendScalars f).obj M :=
  (esAdj f).unit.app M x

/-- Two maps out of an extension of scalars agree as soon as they agree on the canonical
generators. -/
private lemma es_hom_ext {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    {M : ModuleCat.{max v w} R} {N : ModuleCat.{max v w} S}
    {α β : (ModuleCat.extendScalars f).obj M ⟶ N}
    (h : ∀ x : M, α (esOne f M x) = β (esOne f M x)) : α = β :=
  ModuleCat.ExtendScalars.hom_ext h

/-- Extension of scalars sends a canonical generator to a canonical generator. -/
private lemma es_map_one {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    {M M' : ModuleCat.{max v w} R} (g : M ⟶ M') (x : M) :
    (ModuleCat.extendScalars f).map g (esOne f M x) = esOne f M' (g x) :=
  ModuleCat.ExtendScalars.map_tmul f g 1 x

/-- The counit of the extension/restriction adjunction undoes a canonical generator. -/
private lemma es_counit_one {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{max v w} S) (m : M) :
    (esAdj f).counit.app M (esOne f ((ModuleCat.restrictScalars f).obj M) m) = m :=
  ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul f M m

/-- The comparison of extension of scalars along a composite with the composite of extensions
of scalars sends a canonical generator to the iterated canonical generator. -/
private lemma es_comp_one {R S T : Type w} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (M : ModuleCat.{max v w} R) (x : M) :
    (ModuleCat.extendScalarsComp f g).hom.app M (esOne (g.comp f) M x) =
      esOne g ((ModuleCat.extendScalars f).obj M) (esOne f M x) :=
  ModuleCat.extendScalarsComp_hom_app_one_tmul f g M x

/-- Extension of scalars along a composite is the composite of extensions of scalars, with the
composite written as a given homomorphism. -/
private def scalarCompositionIso {R S T : Type w} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (r : R →+* T) (hr : g.comp f = r) :
    ModuleCat.extendScalars.{w, w, max v w} r ≅
      ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g := by
  subst r
  exact ModuleCat.extendScalarsComp f g

/-- The composition isomorphism sends `1 ⊗ x` to `1 ⊗ (1 ⊗ x)`. -/
private lemma scalarCompositionIso_one {R S T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (r : R →+* T) (hr : g.comp f = r)
    (M : ModuleCat.{max v w} R) (x : M) :
    (scalarCompositionIso f g r hr).hom.app M (esOne r M x) =
      esOne g ((ModuleCat.extendScalars f).obj M) (esOne f M x) := by
  subst r
  exact es_comp_one f g M x

/-- Extending scalars along a composite, after restricting along the first factor, maps
canonically to extending scalars along the second factor. -/
private def scalarRestrictionMap {R S T : Type w} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (r : R →+* T) (hr : g.comp f = r) :
    ModuleCat.restrictScalars.{max v w} f ⋙ ModuleCat.extendScalars r ⟶
      ModuleCat.extendScalars g := by
  rw [← hr]
  exact Functor.whiskerLeft (ModuleCat.restrictScalars f)
      (ModuleCat.extendScalarsComp f g).hom ≫
    Functor.whiskerRight (ModuleCat.extendRestrictScalarsAdj f).counit
      (ModuleCat.extendScalars g)

/-- The canonical map sends `1 ⊗ y` to `1 ⊗ y`. -/
private lemma scalarRestrictionMap_one {R S T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (r : R →+* T) (hr : g.comp f = r)
    (N : ModuleCat.{max v w} S) (y : N) :
    (scalarRestrictionMap f g r hr).app N
        (esOne r ((ModuleCat.restrictScalars f).obj N) y) = esOne g N y := by
  subst r
  calc (scalarRestrictionMap f g (g.comp f) rfl).app N
          (esOne (g.comp f) ((ModuleCat.restrictScalars f).obj N) y)
      = (ModuleCat.extendScalars g).map ((esAdj f).counit.app N)
          (esOne g ((ModuleCat.extendScalars f).obj
            ((ModuleCat.restrictScalars f).obj N))
            (esOne f ((ModuleCat.restrictScalars f).obj N) y)) :=
        congrArg (fun z : (ModuleCat.extendScalars g).obj
            ((ModuleCat.extendScalars f).obj
              ((ModuleCat.restrictScalars f).obj N)) =>
          ((ModuleCat.extendScalars g).map ((esAdj f).counit.app N)) z)
          (es_comp_one f g ((ModuleCat.restrictScalars f).obj N) y)
    _ = esOne g N ((esAdj f).counit.app N
          (esOne f ((ModuleCat.restrictScalars f).obj N) y)) :=
        es_map_one g ((esAdj f).counit.app N)
          (esOne f ((ModuleCat.restrictScalars f).obj N) y)
    _ = esOne g N y :=
        congrArg (fun z : N => esOne g N z) (es_counit_one f N y)

/-- The square relating the two ways of reducing a transition map: reduce in two steps, or
reduce directly and then compare. -/
private lemma scalar_reduction_square {R S T U : Type w}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (a : S →+* T) (b : T →+* U)
    (a' : R →+* T) (c : S →+* U) (c' : R →+* U)
    (ha : a.comp f = a') (hc : b.comp a = c)
    (hc' : b.comp a' = c') (hfc : c.comp f = c')
    (M : ModuleCat.{max v w} R) (N : ModuleCat.{max v w} S)
    (t : M ⟶ (ModuleCat.restrictScalars f).obj N) :
    (scalarCompositionIso a' b c' hc').hom.app M ≫
      (ModuleCat.extendScalars b).map
        ((ModuleCat.extendScalars a').map t ≫ (scalarRestrictionMap f a a' ha).app N) =
      ((ModuleCat.extendScalars c').map t ≫ (scalarRestrictionMap f c c' hfc).app N) ≫
        (scalarCompositionIso a b c hc).hom.app N := by
  apply es_hom_ext c'
  intro x
  have hstepA : ((ModuleCat.extendScalars a').map t ≫
      (scalarRestrictionMap f a a' ha).app N) (esOne a' M x) = esOne a N (t x) :=
    Eq.trans (congrArg (fun z : (ModuleCat.extendScalars a').obj
        ((ModuleCat.restrictScalars f).obj N) =>
      ((scalarRestrictionMap f a a' ha).app N) z) (es_map_one a' t x))
      (scalarRestrictionMap_one f a a' ha N (t x))
  have hstepC : ((ModuleCat.extendScalars c').map t ≫
      (scalarRestrictionMap f c c' hfc).app N) (esOne c' M x) = esOne c N (t x) :=
    Eq.trans (congrArg (fun z : (ModuleCat.extendScalars c').obj
        ((ModuleCat.restrictScalars f).obj N) =>
      ((scalarRestrictionMap f c c' hfc).app N) z) (es_map_one c' t x))
      (scalarRestrictionMap_one f c c' hfc N (t x))
  calc ((scalarCompositionIso a' b c' hc').hom.app M ≫
        (ModuleCat.extendScalars b).map
          ((ModuleCat.extendScalars a').map t ≫
            (scalarRestrictionMap f a a' ha).app N)) (esOne c' M x)
      = (ModuleCat.extendScalars b).map
          ((ModuleCat.extendScalars a').map t ≫
            (scalarRestrictionMap f a a' ha).app N)
          (esOne b ((ModuleCat.extendScalars a').obj M) (esOne a' M x)) :=
        congrArg (fun z : (ModuleCat.extendScalars b).obj
            ((ModuleCat.extendScalars a').obj M) =>
          ((ModuleCat.extendScalars b).map
            ((ModuleCat.extendScalars a').map t ≫
              (scalarRestrictionMap f a a' ha).app N)) z)
          (scalarCompositionIso_one a' b c' hc' M x)
    _ = esOne b ((ModuleCat.extendScalars a).obj N)
          (((ModuleCat.extendScalars a').map t ≫
            (scalarRestrictionMap f a a' ha).app N) (esOne a' M x)) :=
        es_map_one b ((ModuleCat.extendScalars a').map t ≫
          (scalarRestrictionMap f a a' ha).app N) (esOne a' M x)
    _ = esOne b ((ModuleCat.extendScalars a).obj N) (esOne a N (t x)) :=
        congrArg (fun z : (ModuleCat.extendScalars a).obj N =>
          esOne b ((ModuleCat.extendScalars a).obj N) z) hstepA
    _ = (scalarCompositionIso a b c hc).hom.app N (esOne c N (t x)) :=
        (scalarCompositionIso_one a b c hc N (t x)).symm
    _ = (((ModuleCat.extendScalars c').map t ≫
          (scalarRestrictionMap f c c' hfc).app N) ≫
          (scalarCompositionIso a b c hc).hom.app N) (esOne c' M x) :=
        (congrArg (fun z : (ModuleCat.extendScalars c).obj N =>
          ((scalarCompositionIso a b c hc).hom.app N) z) hstepC).symm

/-- The canonical restriction comparison is the sheafification of the module-level canonical
map. -/
private theorem canonicalRestrictionComparison_eq_map
    (n k : ℕ) (h : k ≤ n) (G : FiniteLevelSheaf.{u, m} B X ℓ n) :
    FiniteLevelSheaf.canonicalRestrictionComparison B X ℓ n k h G =
      (presheafToSheaf (SmallEtale.topology B X.obj X.property) _).map
        (Functor.whiskerLeft G.obj
          (scalarRestrictionMap (finiteLevelRingHom ℓ n)
            (ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 1 ≤ n + 1)) _)
            (ZMod.castHom (pow_dvd_pow ℓ (reductionExponent_le k n h)) _)
            (by ext x; simp [finiteLevelRingHom]))) := by
  let f := finiteLevelRingHom ℓ n
  let g : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 1)) :=
    ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 1 ≤ n + 1)) _
  let r : ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1)) :=
    ZMod.castHom (pow_dvd_pow ℓ (reductionExponent_le k n h)) _
  have hr : g.comp f = r := by ext x; simp [f, g, r, finiteLevelRingHom]
  let J := SmallEtale.topology B X.obj X.property
  let P := G.obj ⋙ ModuleCat.restrictScalars.{m} f
  let τ : P ⋙ ModuleCat.extendScalars r ⟶ G.obj ⋙ ModuleCat.extendScalars g := by
    rw [← hr]
    exact Functor.whiskerLeft G.obj
      (Functor.whiskerLeft (ModuleCat.restrictScalars f)
        (ModuleCat.extendScalarsComp f g).hom ≫
        Functor.whiskerRight (ModuleCat.extendRestrictScalarsAdj f).counit
          (ModuleCat.extendScalars g))
  have hτ : τ = Functor.whiskerLeft G.obj (scalarRestrictionMap f g r hr) := by
    clear_value r
    subst r
    rfl
  have : J.PreservesSheafification (ModuleCat.extendScalars.{0, 0, m} r) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.extendRestrictScalarsAdj.{m, 0, 0} r)
  have hcancel : (Sheaf.composeAndSheafify J (ModuleCat.extendScalars r)).map
        (inv ((sheafificationAdjunction J _).counit.app (G.restrictScalars B X ℓ n))) ≫
      (presheafToSheafCompComposeAndSheafifyIso J (ModuleCat.extendScalars r)).hom.app P =
      𝟙 _ :=
    cancel_sheaf_comparison J (ModuleCat.extendScalars r) (G.restrictScalars B X ℓ n)
  show (Sheaf.composeAndSheafify J (ModuleCat.extendScalars r)).map
      (inv ((sheafificationAdjunction J _).counit.app (G.restrictScalars B X ℓ n))) ≫
    (presheafToSheafCompComposeAndSheafifyIso J (ModuleCat.extendScalars r)).hom.app P ≫
    (presheafToSheaf J _).map τ = _
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  rw [hcancel]
  exact (Category.id_comp ((presheafToSheaf J _).map τ)).trans
    (congrArg (fun z => (presheafToSheaf J _).map z) hτ)

/-- The inverse of the canonical reduction comparison, written out as a sheafified module-level
map followed by the comparison isomorphism. -/
private theorem canonicalReductionComparison_inv
    (n k : ℕ) (h : k + 1 ≤ n) (G : FiniteLevelSheaf.{u, m} B X ℓ n)
    [(SmallEtale.topology B X.obj X.property).PreservesSheafification
      (ModuleCat.extendScalars.{0, 0, m} (finiteLevelRingHom ℓ k))] :
    (FiniteLevelSheaf.canonicalReductionComparison B X ℓ n k h G).inv =
      (presheafToSheaf (SmallEtale.topology B X.obj X.property) _).map
        (Functor.whiskerLeft G.obj
          (scalarCompositionIso
            (ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 2 ≤ n + 1)) _)
            (finiteLevelRingHom ℓ k)
            (ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 1 ≤ n + 1)) _)
            (by ext x; simp [finiteLevelRingHom])).hom) ≫
      (presheafToSheafCompComposeAndSheafifyIso
        (SmallEtale.topology B X.obj X.property)
        (ModuleCat.extendScalars (finiteLevelRingHom ℓ k))).inv.app
        (G.obj ⋙ ModuleCat.extendScalars
          (ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 2 ≤ n + 1)) _)) := by
  let f : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 2)) :=
    ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 2 ≤ n + 1)) _
  let g := finiteLevelRingHom ℓ k
  let r : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 1)) :=
    ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 1 ≤ n + 1)) _
  have hr : g.comp f = r := by ext x; simp [f, g, r, finiteLevelRingHom]
  let J := SmallEtale.topology B X.obj X.property
  let b := (presheafToSheaf J (ModuleCat.{m} (ZMod (ℓ ^ (k + 1))))).mapIso
    (Functor.isoWhiskerLeft G.obj (ModuleCat.extendScalarsComp f g))
  let b' : (presheafToSheaf J _).obj (G.obj ⋙ ModuleCat.extendScalars r) ≅
      (presheafToSheaf J _).obj
        (G.obj ⋙ (ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g)) := by
    rw [hr] at b
    exact b
  have hb : b'.hom = (presheafToSheaf J _).map
      (Functor.whiskerLeft G.obj (scalarCompositionIso f g r hr).hom) := by
    clear_value r
    subst r
    rfl
  show b'.hom ≫ _ = _
  rw [hb]
  rfl

end ScalarReductionCompatibility

/-- Reduction preserves constructibility, by Tag 0GKB. -/
private theorem reduceTo_constructible
    [Fact ℓ.Prime]
    (n k : ℕ) (h : k ≤ n) (G : FiniteLevelSheaf.{u, m} B X ℓ n)
    (hG : IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) G) :
    IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (k + 1)))
      (FiniteLevelSheaf.reduceTo B X ℓ n k h G) :=
  isConstructibleModuleSheaf_extendScalars B X
    (ZMod (ℓ ^ (n + 1))) (ZMod (ℓ ^ (k + 1)))
    (ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 1 ≤ n + 1)) _) G hG

/-- Restriction of scalars along a surjective ring homomorphism is full. -/
private theorem moduleRestrictScalarsFullOfSurjective
    {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Surjective f) : (ModuleCat.restrictScalars f).Full where
  map_surjective := by
    intro X Y g
    refine ⟨ModuleCat.ofHom {
      toFun := g.hom
      map_add' := g.hom.map_add
      map_smul' := fun s x => by
        obtain ⟨r, rfl⟩ := hf s
        exact g.hom.map_smul r x
    }, ?_⟩
    ext x
    rfl

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))] in
/-- The canonical restriction comparison is always an isomorphism: the coefficient quotient map
is surjective, so restriction of scalars along it is fully faithful and the counit of the
extension/restriction adjunction is invertible. -/
private theorem canonicalRestrictionComparison_isIso
    (n k : ℕ) (h : k ≤ n) (G : FiniteLevelSheaf.{u, m} B X ℓ n) :
    IsIso (FiniteLevelSheaf.canonicalRestrictionComparison B X ℓ n k h G) := by
  let f : ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (n + 1)) := finiteLevelRingHom ℓ n
  have hf : Function.Surjective f :=
    ZMod.castHom_surjective (pow_dvd_pow ℓ (by omega : n + 1 ≤ n + 2))
  have : (ModuleCat.restrictScalars.{m, 0, 0} f).Full :=
    moduleRestrictScalarsFullOfSurjective hf
  have : IsIso (ModuleCat.extendRestrictScalarsAdj.{m, 0, 0} f).counit :=
    (NatTrans.isIso_iff_isIso_app _).2 fun M =>
      Adjunction.instIsIsoAppCounitOfFullOfFaithful _ M
  rw [canonicalRestrictionComparison_eq_map]
  have key : ∀ (r : ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1)))
      (hr : (ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 1 ≤ n + 1)) _ :
        ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 1))).comp f = r),
      IsIso (scalarRestrictionMap f _ r hr) := by
    rintro r rfl
    dsimp [scalarRestrictionMap]
    infer_instance
  have := key (ZMod.castHom (pow_dvd_pow ℓ (reductionExponent_le k n h)) _)
    (by ext x; simp [f, finiteLevelRingHom])
  exact Functor.map_isIso _ _

/-- One step of the reduction sequence at level `k`: reduce the transition map, then compare
with the direct reduction. -/
private noncomputable def reductionStep
    (G : ∀ n, FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : ∀ n, G (n + 1) ⟶ (G n).restrictScalars B X ℓ n)
    (k n : ℕ) (h : k ≤ n) :
    FiniteLevelSheaf.reduceTo B X ℓ (n + 1) k (by omega) (G (n + 1)) ⟶
      FiniteLevelSheaf.reduceTo B X ℓ n k h (G n) :=
  (Sheaf.composeAndSheafify
      (SmallEtale.topology B X.obj X.property)
      (ModuleCat.extendScalars.{0, 0, m}
        (ZMod.castHom (pow_dvd_pow ℓ (reductionExponent_le k n h)) _ :
          ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1))))).map (t n) ≫
    FiniteLevelSheaf.canonicalRestrictionComparison B X ℓ n k h (G n)

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))] in
/-- Past the stabilization index, a reduction step is an isomorphism. -/
private theorem reductionStep_isIso
    (G : ∀ n, FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : ∀ n, G (n + 1) ⟶ (G n).restrictScalars B X ℓ n)
    (k n : ℕ) (h : k ≤ n)
    (hcmp : IsIso (FiniteLevelSheaf.canonicalRestrictionComparison B X ℓ n k h (G n)))
    (heventually : ∀ (k : ℕ), ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → (h : k ≤ n) →
      IsIso ((Sheaf.composeAndSheafify
        (SmallEtale.topology B X.obj X.property)
        (ModuleCat.extendScalars.{0, 0, m}
          (ZMod.castHom (pow_dvd_pow ℓ (reductionExponent_le k n h)) _ :
            ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1))))).map (t n)))
    (hn : (heventually k).choose ≤ n) :
    IsIso (reductionStep B X ℓ G t k n h) := by
  have hstep := (Classical.choose_spec (heventually k)) n hn h
  let J := SmallEtale.topology B X.obj X.property
  let q : ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1)) :=
    ZMod.castHom (pow_dvd_pow ℓ (reductionExponent_le k n h)) _
  change IsIso ((CategoryTheory.presheafToSheaf J
    (ModuleCat.{m} (ZMod (ℓ ^ (k + 1))))).map
      (Functor.whiskerRight (t n).hom (ModuleCat.extendScalars.{0, 0, m} q))) at hstep
  have : IsIso (FiniteLevelSheaf.canonicalRestrictionComparison B X ℓ n k h (G n)) := hcmp
  dsimp [reductionStep]
  infer_instance

/-- The inverse sequence of reductions to level `k` of the levels from `N` upwards. -/
private noncomputable def reductionTailSequence
    (G : ∀ n, FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : ∀ n, G (n + 1) ⟶ (G n).restrictScalars B X ℓ n)
    (k N : ℕ) (hkN : k ≤ N) : ℕᵒᵖ ⥤ FiniteLevelSheaf.{u, m} B X ℓ k :=
  Functor.ofOpSequence (X := fun j =>
      FiniteLevelSheaf.reduceTo B X ℓ (N + j) k (by omega) (G (N + j)))
    (fun j => reductionStep B X ℓ G t k (N + j) (by omega))

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))] in
/-- Past the stabilization index, the reduction sequence is eventually constant. -/
private theorem reductionTailSequence_eventuallyConstant
    (G : ∀ n, FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : ∀ n, G (n + 1) ⟶ (G n).restrictScalars B X ℓ n)
    (heventually : ∀ (k : ℕ), ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → (h : k ≤ n) →
      IsIso ((Sheaf.composeAndSheafify
        (SmallEtale.topology B X.obj X.property)
        (ModuleCat.extendScalars.{0, 0, m}
          (ZMod.castHom (pow_dvd_pow ℓ (reductionExponent_le k n h)) _ :
            ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1))))).map (t n)))
    (k N : ℕ) (hN : (heventually k).choose ≤ N) (hk : k ≤ N) :
    (reductionTailSequence B X ℓ G t k N hk).IsEventuallyConstantTo (Opposite.op 0) := by
  let R := reductionTailSequence B X ℓ G t k N hk
  have hseq : ∀ d : ℕ, IsIso (R.map (homOfLE (show 0 ≤ d by omega)).op) := by
    intro d
    induction d with
    | zero =>
        simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
        infer_instance
    | succ d ih =>
        have hcomp : homOfLE (show 0 ≤ d + 1 by omega) =
            homOfLE (show 0 ≤ d by omega) ≫
              homOfLE (show d ≤ d + 1 by omega) :=
          homOfLE_comp (show 0 ≤ d by omega) (show d ≤ d + 1 by omega)
        rw [hcomp, op_comp, Functor.map_comp]
        have hstep : IsIso (reductionStep B X ℓ G t k (N + d) (by omega)) := by
          have hc := canonicalRestrictionComparison_isIso B X ℓ (N + d) k (by omega)
            (G (N + d))
          exact reductionStep_isIso B X ℓ G t k (N + d) (by omega) hc
            heventually (by omega)
        have hstep' : IsIso (R.map (homOfLE (show d ≤ d + 1 by omega)).op) := by
          show IsIso ((reductionTailSequence B X ℓ G t k N hk).map
            (homOfLE (show d ≤ d + 1 by omega)).op)
          dsimp [reductionTailSequence]
          have hhom : homOfLE (show d ≤ d + 1 by omega) =
              homOfLE (Nat.le_add_right d 1) := Subsingleton.elim _ _
          rw [hhom, Functor.ofOpSequence_map_homOfLE_succ]
          exact hstep
        exact IsIso.comp_isIso' hstep' ih
  rintro ⟨d⟩ f
  have hf : f = (homOfLE (Nat.zero_le d)).op := Subsingleton.elim _ _
  rw [hf]
  exact hseq d

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))] in
/-- Reductions to level `k` of equal indices agree. -/
private theorem reduceTo_congrIndex
    (G : ∀ n, FiniteLevelSheaf.{u, m} B X ℓ n) {n n' : ℕ} (h : n = n')
    (k : ℕ) (hn : k ≤ n) (hn' : k ≤ n') :
    FiniteLevelSheaf.reduceTo B X ℓ n k hn (G n) =
      FiniteLevelSheaf.reduceTo B X ℓ n' k hn' (G n') := by
  cases h
  rfl

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))] in
/-- The successor maps of the reduction sequence are the reduction steps. -/
private theorem reductionTailSequence_map_succ
    (G : ∀ n, FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : ∀ n, G (n + 1) ⟶ (G n).restrictScalars B X ℓ n)
    (k N : ℕ) (hkN : k ≤ N) (d : ℕ) :
    (reductionTailSequence B X ℓ G t k N hkN).map
      (homOfLE (Nat.le_add_right d 1)).op =
        reductionStep B X ℓ G t k (N + d) (by omega) := by
  dsimp [reductionTailSequence]
  rw [Functor.ofOpSequence_map_homOfLE_succ]

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))] in
/-- The objects of the reduction sequence are the reductions of the levels above `N`. -/
private theorem reductionTailSequence_obj_eq
    (G : ∀ n, FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : ∀ n, G (n + 1) ⟶ (G n).restrictScalars B X ℓ n)
    (k N : ℕ) (hkN : k ≤ N) (d n : ℕ) (hnd : N + d = n) :
    (reductionTailSequence B X ℓ G t k N hkN).obj (Opposite.op d) =
      FiniteLevelSheaf.reduceTo B X ℓ n k (by omega) (G n) := by
  show FiniteLevelSheaf.reduceTo B X ℓ (N + d) k (by omega) (G (N + d)) = _
  exact reduceTo_congrIndex B X ℓ G hnd k (by omega) (by omega)

/-- The isomorphism between the stable value of the reduction sequence at level `k` and the
reduction of any sufficiently high level. -/
private noncomputable def stableReductionIso
    (G : ∀ n, FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : ∀ n, G (n + 1) ⟶ (G n).restrictScalars B X ℓ n)
    (heventually : ∀ (k : ℕ), ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → (h : k ≤ n) →
      IsIso ((Sheaf.composeAndSheafify
        (SmallEtale.topology B X.obj X.property)
        (ModuleCat.extendScalars.{0, 0, m}
          (ZMod.castHom (pow_dvd_pow ℓ (reductionExponent_le k n h)) _ :
            ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1))))).map (t n)))
    (k N n d : ℕ) (hnd : N + d = n) (_hn : N ≤ n)
    (hk : k ≤ n) (hkN : k ≤ N)
    (hN : (heventually k).choose ≤ N) :
    FiniteLevelSheaf.reduceTo B X ℓ N k (by omega) (G N) ≅
      FiniteLevelSheaf.reduceTo B X ℓ n k hk (G n) := by
  let R := reductionTailSequence B X ℓ G t k N hkN
  have hmap : IsIso (R.map (homOfLE (show 0 ≤ d by omega)).op) :=
    reductionTailSequence_eventuallyConstant B X ℓ G t heventually k N hN hkN
      (homOfLE (show 0 ≤ d by omega)).op
  let e := (asIso (R.map (homOfLE (show 0 ≤ d by omega)).op)).symm
  have hobjN : R.obj (Opposite.op 0) =
      FiniteLevelSheaf.reduceTo B X ℓ N k (by omega) (G N) :=
    reductionTailSequence_obj_eq B X ℓ G t k N hkN 0 N (by omega)
  have hobj : R.obj (Opposite.op d) =
      FiniteLevelSheaf.reduceTo B X ℓ n k hk (G n) :=
    reductionTailSequence_obj_eq B X ℓ G t k N hkN d n hnd
  exact (eqToIso hobjN).symm ≪≫ e ≪≫ eqToIso hobj

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))] in
/-- The stable isomorphisms are compatible with one reduction step. -/
private theorem stableReductionIso_natural
    (G : ∀ n, FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : ∀ n, G (n + 1) ⟶ (G n).restrictScalars B X ℓ n)
    (heventually : ∀ (k : ℕ), ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → (h : k ≤ n) →
      IsIso ((Sheaf.composeAndSheafify
        (SmallEtale.topology B X.obj X.property)
        (ModuleCat.extendScalars.{0, 0, m}
          (ZMod.castHom (pow_dvd_pow ℓ (reductionExponent_le k n h)) _ :
            ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1))))).map (t n)))
    (k N n d d₁ : ℕ) (hnd : N + d = n)
    (hnd₁ : N + d₁ = n + 1) (hd : d₁ = d + 1)
    (hN : (heventually k).choose ≤ N) (hkN : k ≤ N)
    (hn : N ≤ n) :
    (stableReductionIso B X ℓ G t heventually k N (n + 1) d₁
      hnd₁ (by omega) (by omega) hkN hN).hom ≫
        reductionStep B X ℓ G t k n (by omega) =
    (stableReductionIso B X ℓ G t heventually k N n d hnd hn (by omega) hkN hN).hom := by
  cases hd
  have hnd1 : N + (d + 1) = n + 1 := by omega
  let R := reductionTailSequence B X ℓ G t k N hkN
  have hmapcomp : R.map (homOfLE (show 0 ≤ d + 1 by omega)).op =
      R.map (homOfLE (show d ≤ d + 1 by omega)).op ≫
        R.map (homOfLE (show 0 ≤ d by omega)).op := by
    have hbase : homOfLE (show 0 ≤ d by omega) ≫
        homOfLE (show d ≤ d + 1 by omega) =
          homOfLE (show 0 ≤ d + 1 by omega) := Subsingleton.elim _ _
    calc
      R.map (homOfLE (show 0 ≤ d + 1 by omega)).op =
          R.map ((homOfLE (show 0 ≤ d by omega) ≫
            homOfLE (show d ≤ d + 1 by omega)).op) := by
              congr 1
      _ = R.map (homOfLE (show d ≤ d + 1 by omega)).op ≫
          R.map (homOfLE (show 0 ≤ d by omega)).op := by
            rw [op_comp, R.map_comp]
  let f := R.map (homOfLE (show 0 ≤ d by omega)).op
  let g := R.map (homOfLE (show d ≤ d + 1 by omega)).op
  let f' := R.map (homOfLE (show 0 ≤ d + 1 by omega)).op
  have hf : IsIso f :=
    reductionTailSequence_eventuallyConstant B X ℓ G t heventually k N hN hkN
      (homOfLE (show 0 ≤ d by omega)).op
  have hf' : IsIso f' :=
    reductionTailSequence_eventuallyConstant B X ℓ G t heventually k N hN hkN
      (homOfLE (show 0 ≤ d + 1 by omega)).op
  have hkey : (asIso f').inv ≫ g = (asIso f).inv := by
    apply (cancel_mono f).mp
    calc
      (asIso (R.map (homOfLE (show 0 ≤ d + 1 by omega)).op)).inv ≫
          R.map (homOfLE (show d ≤ d + 1 by omega)).op ≫
            R.map (homOfLE (show 0 ≤ d by omega)).op =
        (asIso (R.map (homOfLE (show 0 ≤ d + 1 by omega)).op)).inv ≫
          (R.map (homOfLE (show d ≤ d + 1 by omega)).op ≫
            R.map (homOfLE (show 0 ≤ d by omega)).op) := by
              simp
      _ = (asIso (R.map (homOfLE (show 0 ≤ d + 1 by omega)).op)).inv ≫
          R.map (homOfLE (show 0 ≤ d + 1 by omega)).op := by rw [← hmapcomp]
      _ = 𝟙 _ := by simp
      _ = (asIso (R.map (homOfLE (show 0 ≤ d by omega)).op)).inv ≫
          R.map (homOfLE (show 0 ≤ d by omega)).op := by simp
  have hobjN : R.obj (Opposite.op 0) =
      FiniteLevelSheaf.reduceTo B X ℓ N k hkN (G N) :=
    reductionTailSequence_obj_eq B X ℓ G t k N hkN 0 N (by omega)
  have hobj0 : R.obj (Opposite.op d) =
      FiniteLevelSheaf.reduceTo B X ℓ n k (by omega) (G n) :=
    reductionTailSequence_obj_eq B X ℓ G t k N hkN d n hnd
  have hobj1 : R.obj (Opposite.op (d + 1)) =
      FiniteLevelSheaf.reduceTo B X ℓ (n + 1) k (by omega) (G (n + 1)) :=
    reductionTailSequence_obj_eq B X ℓ G t k N hkN (d + 1) (n + 1) hnd1
  have hstep : (eqToIso hobj1).hom ≫ reductionStep B X ℓ G t k n (by omega) =
      g ≫ (eqToIso hobj0).hom := by
    cases hnd
    cases hobj1
    cases hobj0
    rw [← reductionTailSequence_map_succ B X ℓ G t k N hkN d]
    rfl
  have hnat : (eqToIso hobjN).inv ≫ (asIso f').inv ≫
      (eqToIso hobj1).hom ≫ reductionStep B X ℓ G t k n (by omega) =
      (eqToIso hobjN).inv ≫ (asIso f).inv ≫ (eqToIso hobj0).hom := by
    calc
      _ = (eqToIso hobjN).inv ≫ ((asIso f').inv ≫ g) ≫
          (eqToIso hobj0).hom := by
            rw [← Category.assoc, hstep, Category.assoc]
            simp only [Category.assoc]
      _ = (eqToIso hobjN).inv ≫ (asIso f).inv ≫
          (eqToIso hobj0).hom := by rw [hkey]
  simpa [stableReductionIso, Iso.trans_hom, Iso.symm_hom, R, f, f', g,
    hobjN, hobj0, hobj1, hnd1, Nat.add_sub_cancel_left, Category.assoc] using hnat

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))] in
/-- A reduction step commutes with the canonical quotient map between successive reductions. -/
private theorem canonicalReductionTransition_natural_reductionStep
    (G : ∀ n, FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : ∀ n, G (n + 1) ⟶ (G n).restrictScalars B X ℓ n)
    (k n : ℕ) (h : k + 1 ≤ n) :
    reductionStep B X ℓ G t (k + 1) n (by omega) ≫
        FiniteLevelSheaf.canonicalReductionTransition B X ℓ n k h (G n) =
      FiniteLevelSheaf.canonicalReductionTransition B X ℓ (n + 1) k (by omega)
          (G (n + 1)) ≫
        (sheafCompose (SmallEtale.topology B X.obj X.property)
          (ModuleCat.restrictScalars.{m, 0, 0} (finiteLevelRingHom ℓ k))).map
          (reductionStep B X ℓ G t k n (by omega)) := by
  let J := SmallEtale.topology B X.obj X.property
  let adj := Sheaf.adjunction J
    (ModuleCat.extendRestrictScalarsAdj.{m, 0, 0} (finiteLevelRingHom ℓ k))
  dsimp only [FiniteLevelSheaf.canonicalReductionTransition]
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  apply congrArg (adj.homEquiv _ _)
  have hsucc : k + 1 ≤ n + 1 := Nat.le_succ_of_le h
  have hepi : Epi (FiniteLevelSheaf.canonicalReductionComparison B X ℓ (n + 1) k
      hsucc (G (n + 1))).inv := IsIso.epi_of_iso _
  have hmono : Mono (FiniteLevelSheaf.canonicalReductionComparison B X ℓ n k h
      (G n)).inv := IsIso.mono_of_iso _
  apply (cancel_epi
    (FiniteLevelSheaf.canonicalReductionComparison B X ℓ (n + 1) k hsucc
      (G (n + 1))).inv).mp
  apply (cancel_mono
    (FiniteLevelSheaf.canonicalReductionComparison B X ℓ n k h (G n)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id]
  let f := finiteLevelRingHom ℓ n
  let a : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 2)) :=
    ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 2 ≤ n + 1)) _
  let b := finiteLevelRingHom ℓ k
  let a' : ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 2)) :=
    ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 2 ≤ n + 2)) _
  let c : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 1)) :=
    ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 1 ≤ n + 1)) _
  let c' : ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1)) :=
    ZMod.castHom (pow_dvd_pow ℓ (reductionExponent_le k n (Nat.le_of_succ_le h))) _
  have ha : a.comp f = a' := by ext x; simp [a, f, a', finiteLevelRingHom]
  have hc : b.comp a = c := by ext x; simp [b, a, c, finiteLevelRingHom]
  have hc' : b.comp a' = c' := by ext x; simp [b, a', c', finiteLevelRingHom]
  have hfc : c.comp f = c' := by ext x; simp [c, f, c', finiteLevelRingHom]
  let ST := presheafToSheaf J (ModuleCat.{m} (ZMod (ℓ ^ (k + 2))))
  let SU := presheafToSheaf J (ModuleCat.{m} (ZMod (ℓ ^ (k + 1))))
  let ρT := Functor.whiskerRight (t n).hom (ModuleCat.extendScalars a') ≫
    Functor.whiskerLeft (G n).obj (scalarRestrictionMap f a a' ha)
  let ρU := Functor.whiskerRight (t n).hom (ModuleCat.extendScalars c') ≫
    Functor.whiskerLeft (G n).obj (scalarRestrictionMap f c c' hfc)
  let βP := Functor.whiskerLeft (G (n + 1)).obj
    (scalarCompositionIso a' b c' hc').hom
  let βQ := Functor.whiskerLeft (G n).obj (scalarCompositionIso a b c hc).hom
  have : J.PreservesSheafification (ModuleCat.extendScalars.{0, 0, m} b) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.extendRestrictScalarsAdj.{m, 0, 0} b)
  let α := presheafToSheafCompComposeAndSheafifyIso J (ModuleCat.extendScalars b)
  have stepT : reductionStep B X ℓ G t (k + 1) n (by omega) = ST.map ρT := by
    dsimp only [reductionStep]
    rw [canonicalRestrictionComparison_eq_map]
    exact (ST.map_comp _ _).symm
  have stepU : reductionStep B X ℓ G t k n (by omega) = SU.map ρU := by
    dsimp only [reductionStep]
    rw [canonicalRestrictionComparison_eq_map]
    exact (SU.map_comp _ _).symm
  rw [canonicalReductionComparison_inv, canonicalReductionComparison_inv, stepT, stepU]
  show (SU.map βP ≫ α.inv.app ((G (n + 1)).obj ⋙ ModuleCat.extendScalars a')) ≫
      (Sheaf.composeAndSheafify J (ModuleCat.extendScalars b)).map (ST.map ρT) =
    SU.map ρU ≫ (SU.map βQ ≫ α.inv.app ((G n).obj ⋙ ModuleCat.extendScalars a))
  have hnat := α.inv.naturality ρT
  change SU.map (Functor.whiskerRight ρT (ModuleCat.extendScalars b)) ≫
      α.inv.app ((G n).obj ⋙ ModuleCat.extendScalars a) =
    α.inv.app ((G (n + 1)).obj ⋙ ModuleCat.extendScalars a') ≫
      (Sheaf.composeAndSheafify J (ModuleCat.extendScalars b)).map
        (ST.map ρT) at hnat
  rw [Category.assoc, ← hnat, ← Category.assoc, ← SU.map_comp, ← Category.assoc,
    ← SU.map_comp]
  congr 1
  exact SU.congr_map (NatTrans.ext (funext fun V =>
    scalar_reduction_square f a b a' c c' ha hc hc' hfc
      ((G (n + 1)).obj.obj V) ((G n).obj.obj V) ((t n).hom.app V)))

/-- The composite of `d` consecutive reduction steps down to level `k` from index `m + d`. -/
private noncomputable def reductionPath
    (G : ∀ n, FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : ∀ n, G (n + 1) ⟶ (G n).restrictScalars B X ℓ n)
    (k M : ℕ) (hkM : k ≤ M) : (d : ℕ) →
      FiniteLevelSheaf.reduceTo B X ℓ (M + d) k (by omega) (G (M + d)) ⟶
        FiniteLevelSheaf.reduceTo B X ℓ M k hkM (G M)
  | 0 => 𝟙 _
  | d + 1 =>
      reductionStep B X ℓ G t k (M + d) (by omega) ≫
        reductionPath G t k M hkM d

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))] in
/-- A reduction path commutes with the canonical quotient map between successive reductions. -/
private theorem reductionPath_natural_canonicalTransition
    (G : ∀ n, FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : ∀ n, G (n + 1) ⟶ (G n).restrictScalars B X ℓ n)
    (k M d : ℕ) (h : k + 1 ≤ M) :
    reductionPath B X ℓ G t (k + 1) M h d ≫
        FiniteLevelSheaf.canonicalReductionTransition B X ℓ M k h (G M) =
      FiniteLevelSheaf.canonicalReductionTransition B X ℓ (M + d) k (by omega)
          (G (M + d)) ≫
        (sheafCompose (SmallEtale.topology B X.obj X.property)
          (ModuleCat.restrictScalars.{m, 0, 0} (finiteLevelRingHom ℓ k))).map
    (reductionPath B X ℓ G t k M (by omega) d) := by
  induction d with
  | zero => simp [reductionPath]
  | succ d ih =>
      rw [reductionPath.eq_def]
      rw [Category.assoc]
      rw [ih]
      rw [← Category.assoc]
      rw [canonicalReductionTransition_natural_reductionStep
        B X ℓ G t k (M + d) (by omega)]
      have hpath : reductionPath B X ℓ G t k M (by omega) (d + 1) =
          reductionStep B X ℓ G t k (M + d) (by omega) ≫
            reductionPath B X ℓ G t k M (by omega) d := rfl
      rw [hpath]
      rfl

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))] in
/-- Past the stabilization index, a reduction path is an isomorphism. -/
private theorem reductionPath_isIso
    (G : ∀ n, FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : ∀ n, G (n + 1) ⟶ (G n).restrictScalars B X ℓ n)
    (heventually : ∀ (k : ℕ), ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → (h : k ≤ n) →
      IsIso ((Sheaf.composeAndSheafify
        (SmallEtale.topology B X.obj X.property)
        (ModuleCat.extendScalars.{0, 0, m}
          (ZMod.castHom (pow_dvd_pow ℓ (reductionExponent_le k n h)) _ :
            ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1))))).map (t n)))
    (k M d : ℕ) (hM : (heventually k).choose ≤ M) (hkM : k ≤ M) :
    IsIso (reductionPath B X ℓ G t k M hkM d) := by
  induction d with
  | zero =>
      show IsIso (𝟙 _)
      infer_instance
  | succ d ih =>
      have hcmp := canonicalRestrictionComparison_isIso B X ℓ (M + d) k (by omega)
        (G (M + d))
      have hs := reductionStep_isIso B X ℓ G t k (M + d) (by omega) hcmp
        heventually (by omega)
      rw [reductionPath.eq_def]
      have := hs
      have := ih
      infer_instance

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))] in
/-- The stable isomorphisms are compatible with reduction paths. -/
private theorem stableReductionIso_natural_path
    (G : ∀ n, FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : ∀ n, G (n + 1) ⟶ (G n).restrictScalars B X ℓ n)
    (heventually : ∀ (k : ℕ), ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → (h : k ≤ n) →
      IsIso ((Sheaf.composeAndSheafify
        (SmallEtale.topology B X.obj X.property)
        (ModuleCat.extendScalars.{0, 0, m}
          (ZMod.castHom (pow_dvd_pow ℓ (reductionExponent_le k n h)) _ :
            ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1))))).map (t n)))
    (k N M d r : ℕ) (hNM : N + d = M)
    (hN : (heventually k).choose ≤ N) (hkN : k ≤ N) (hM : N ≤ M) :
    (stableReductionIso B X ℓ G t heventually k N (M + r) (d + r)
      (by omega) (by omega) (by omega) hkN hN).hom ≫
    reductionPath B X ℓ G t k M (by omega) r =
      (stableReductionIso B X ℓ G t heventually k N M d hNM (by omega) (by omega)
        hkN hN).hom := by
  induction r with
  | zero => simp [reductionPath]
  | succ r ih =>
      have hs := stableReductionIso_natural B X ℓ G t heventually k N (M + r)
        (d + r) (d + r + 1) (by omega) (by omega) (by omega) hN hkN (by omega)
      show (stableReductionIso B X ℓ G t heventually k N (M + r + 1) (d + r + 1)
          (by omega) (by omega) (by omega) hkN hN).hom ≫
        (reductionStep B X ℓ G t k (M + r) (by omega) ≫
          reductionPath B X ℓ G t k M (by omega) r) =
        (stableReductionIso B X ℓ G t heventually k N M d hNM (by omega) (by omega)
          hkN hN).hom
      rw [← Category.assoc, hs]
      exact ih

/-- **Stacks 03UN.** Eventually constant reductions of a constructible inverse system give an
ℓ-adic sheaf whose levels are the stable values of those reductions. -/
@[stacks 03UN, sga "4½ Rapport 2.6" "ess.const ⇒ Zℓ-sheaf"]
public theorem exists_lAdicSheaf_of_eventuallyConstant_reductions
    [IsNoetherian X.obj] [Fact ℓ.Prime]
    (G : ∀ n, FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : ∀ n, G (n + 1) ⟶ (G n).restrictScalars B X ℓ n)
    (hG : ∀ n, IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) (G n))
    (heventually : ∀ (k : ℕ), ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → (h : k ≤ n) →
      IsIso ((Sheaf.composeAndSheafify
        (SmallEtale.topology B X.obj X.property)
        (ModuleCat.extendScalars.{0, 0, m}
          (ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 1 ≤ n + 2)) _ :
            ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1))))).map (t n))) :
    ∃ F : LAdicSheaf.{u, m} B X ℓ, ∃ N : ℕ → ℕ,
      ∃ e : ∀ (k n : ℕ), N k ≤ n → (h : k ≤ n) →
        F.level k ≅ FiniteLevelSheaf.reduceTo B X ℓ n k h (G n),
      (∀ (k n : ℕ) (hn : N k ≤ n) (h : k ≤ n),
        (e k (n + 1) (by omega) (by omega)).hom ≫
          ((Sheaf.composeAndSheafify
            (SmallEtale.topology B X.obj X.property)
            (ModuleCat.extendScalars.{0, 0, m}
              (ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 1 ≤ n + 2)) _ :
                ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1))))).map (t n)) ≫
          (FiniteLevelSheaf.canonicalRestrictionComparison B X ℓ n k h (G n)) =
          (e k n hn h).hom) ∧
      (∀ (k n : ℕ) (hn₁ : N k ≤ n) (hn₂ : N (k + 1) ≤ n)
          (h : k + 1 ≤ n),
        F.transition k ≫
          (sheafCompose (SmallEtale.topology B X.obj X.property)
            (ModuleCat.restrictScalars.{m, 0, 0}
              (finiteLevelRingHom ℓ k))).map
            ((e k n hn₁ (by omega)).hom) =
        (e (k + 1) n hn₂ h).hom ≫
          (FiniteLevelSheaf.canonicalReductionTransition B X ℓ n k h (G n))) := by
  classical
  let N : ℕ → ℕ := fun k => max (Classical.choose (heventually k)) k
  have hN₁ : ∀ k, (Classical.choose (heventually k)) ≤ N k := fun k => le_max_left _ _
  have hN₂ : ∀ k, k ≤ N k := fun k => le_max_right _ _
  let L : ∀ k, FiniteLevelSheaf.{u, m} B X ℓ k := fun k =>
    FiniteLevelSheaf.reduceTo B X ℓ (N k) k (hN₂ k) (G (N k))
  let e : ∀ (k n : ℕ), N k ≤ n → (h : k ≤ n) →
      L k ≅ FiniteLevelSheaf.reduceTo B X ℓ n k h (G n) := fun k n hn h =>
    stableReductionIso B X ℓ G t heventually k (N k) n (n - N k)
      (by omega) hn h (hN₂ k) (hN₁ k)
  let tr : ∀ k, L (k + 1) ⟶ (L k).restrictScalars B X ℓ k := fun k =>
    (e (k + 1) (max (N k) (N (k + 1))) (le_max_right _ _)
      (le_trans (hN₂ (k + 1)) (le_max_right _ _))).hom ≫
      FiniteLevelSheaf.canonicalReductionTransition B X ℓ
        (max (N k) (N (k + 1))) k
        (le_trans (hN₂ (k + 1)) (le_max_right _ _))
        (G (max (N k) (N (k + 1)))) ≫
      (sheafCompose (SmallEtale.topology B X.obj X.property)
        (ModuleCat.restrictScalars.{m, 0, 0} (finiteLevelRingHom ℓ k))).map
        (e k (max (N k) (N (k + 1))) (le_max_left _ _)
          (le_trans (hN₂ k) (le_max_left _ _))).inv
  let F : LAdicSheaf.{u, m} B X ℓ := {
    level := L
    constructible := fun k => reduceTo_constructible B X ℓ (N k) k (hN₂ k)
      (G (N k)) (hG (N k))
    transition := tr
    reduction_isIso := by
      intro k
      let M := max (N k) (N (k + 1))
      let ekp := e (k + 1) M (le_max_right _ _)
        (le_trans (hN₂ (k + 1)) (le_max_right _ _))
      let ek := e k M (le_max_left _ _) (le_trans (hN₂ k) (le_max_left _ _))
      let cmp := FiniteLevelSheaf.canonicalReductionComparison B X ℓ M k
        (le_trans (hN₂ (k + 1)) (le_max_right _ _)) (G M)
      let adj := Sheaf.adjunction (SmallEtale.topology B X.obj X.property)
        (ModuleCat.extendRestrictScalarsAdj.{m, 0, 0} (finiteLevelRingHom ℓ k))
      have hEq : FiniteLevelSheaf.scalarReductionMap B X ℓ k (L (k + 1)) (L k)
          (tr k) =
          (Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property)
            (ModuleCat.extendScalars.{0, 0, m} (finiteLevelRingHom ℓ k))).map
              ekp.hom ≫ cmp.hom ≫ ek.inv := by
        apply (adj.homEquiv _ _).injective
        dsimp [FiniteLevelSheaf.scalarReductionMap, tr,
          FiniteLevelSheaf.canonicalReductionTransition]
        rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm]
        simp [adj, ekp, ek, cmp, M]
      have hfirst : IsIso ((Sheaf.composeAndSheafify
          (SmallEtale.topology B X.obj X.property)
          (ModuleCat.extendScalars.{0, 0, m}
            (finiteLevelRingHom ℓ k))).map ekp.hom) :=
        Functor.map_isIso _ _
      have hcmp : IsIso cmp.hom := Iso.isIso_hom cmp
      have hlast : IsIso ek.inv := Iso.isIso_inv ek
      rw [hEq]
      infer_instance
  }
  refine ⟨F, N, e, ?_, ?_⟩
  · intro k n hn h
    show (e k (n + 1) (by omega) (by omega)).hom ≫
      reductionStep B X ℓ G t k n h = (e k n hn h).hom
    dsimp only [e]
    exact stableReductionIso_natural B X ℓ G t heventually k (N k) n
      (n - N k) ((n + 1) - N k) (by omega) (by omega) (by omega)
      (hN₁ k) (hN₂ k) hn
  · intro k n hn₁ hn₂ h
    let M := max (N k) (N (k + 1))
    have hkM : k + 1 ≤ M := le_trans (hN₂ (k + 1)) (le_max_right _ _)
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show M ≤ n from max_le hn₁ hn₂)
    let R := sheafCompose (SmallEtale.topology B X.obj X.property)
      (ModuleCat.restrictScalars.{m, 0, 0} (finiteLevelRingHom ℓ k))
    have hepath (j : ℕ) (hj : N j ≤ M) :
        (e j (M + d) (by omega) (by have := hN₂ j; omega)).hom ≫
          reductionPath B X ℓ G t j M (by have := hN₂ j; omega) d =
        (e j M hj (le_trans (hN₂ j) hj)).hom := by
      dsimp only [e]
      have hd : M + d - N j = (M - N j) + d := by omega
      simp only [hd]
      exact stableReductionIso_natural_path B X ℓ G t heventually j (N j) M
        (M - N j) d (by omega) (hN₁ j) (hN₂ j) hj
    let p := reductionPath B X ℓ G t k M (by omega) d
    have : IsIso p := reductionPath_isIso B X ℓ G t heventually k M d
      (le_trans (hN₁ k) (le_max_left _ _)) (by omega)
    apply (cancel_mono (R.map p)).mp
    show (tr k ≫ R.map (e k (M + d) _ _).hom) ≫ R.map p =
      ((e (k + 1) (M + d) _ _).hom ≫
        FiniteLevelSheaf.canonicalReductionTransition B X ℓ (M + d) k h
          (G (M + d))) ≫ R.map p
    rw [Category.assoc, ← R.map_comp, hepath k (le_max_left _ _)]
    have hpNat := reductionPath_natural_canonicalTransition B X ℓ G t k M d hkM
    change _ = _ ≫ R.map p at hpNat
    simp only [Category.assoc]
    rw [← hpNat, ← Category.assoc, hepath (k + 1) (le_max_right _ _)]
    dsimp only [tr, R, M]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]

end AlgebraicGeometry.SmallEtale

end
