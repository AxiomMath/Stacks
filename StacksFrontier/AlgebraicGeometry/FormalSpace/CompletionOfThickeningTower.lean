module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineMcQuillan
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence
public import StacksFrontier.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The completion of a scheme along a closed subset, through a cofinal tower of thickenings

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an object of the big fppf site
of `S` and let `T` be a set of points of its underlying scheme. The completion `X_{/T}` of
Stacks 0AMC is the fppf sheafification of the subfunctor of sections of `X` whose point-set image
lies in `T`.

A *cofinal tower* for `(X, T)` is a sequence of objects `Y 0 ⟶ Y 1 ⟶ Y 2 ⟶ ⋯` of the site with
compatible monomorphisms `ι n : Y n ⟶ X` landing in `T`, such that every morphism from an *affine*
object of the site to `X` with image in `T` factors through some `ι n`. The typical example is a
sequence of closed subschemes `X_n` of a locally Noetherian `X` squeezed between powers of an
ideal sheaf with support `T`; the factorization property for those is
`AlgebraicGeometry.Scheme.Hom.exists_pow_le_ker_of_range_subset_support` of
`StacksFrontier.AlgebraicGeometry.IdealSheaf.Subscheme`.

The completion only depends on the tower: if the same tower `Y` embeds as a cofinal tower in
`(X, T)` and in `(X', T')`, the two completions are canonically isomorphic, compatibly with the
maps from the stages `Y n`. In particular, given isomorphisms `X_n ≅ X'_n` over `S` of cofinal
towers of thickenings of `X` and `X'`, compatible with the inclusions `X_n ⊆ X_{n+1}`, the
completions `X_{/T}` and `X'_{/T'}` are isomorphic: take `Y n = X_n`, `ι n` its inclusion into `X`
and `ι' n` the composite `X_n ≅ X'_n ⊆ X'`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsCofinalTower`: the conditions above.
* `AlgebraicGeometry.FormalSpace.towerSubfunctor`: the sections of `X` factoring through some
  stage of the tower.
* `AlgebraicGeometry.FormalSpace.completionSheafIsoOfCofinalTower`: the isomorphism of completions
  `X_{/T} ≅ X'_{/T'}` induced by a common cofinal tower.
* `AlgebraicGeometry.FormalSpace.towerStageToCompletion`: the morphism from the presheaf
  represented by a stage of the tower into the completion.

## Main results

* `AlgebraicGeometry.FormalSpace.isIso_towerSheafToCompletion`: the sheafified tower subfunctor is
  the completion.
* `AlgebraicGeometry.FormalSpace.towerStageToCompletion_comp_completionSheafIsoOfCofinalTower_hom`:
  the isomorphism of completions is compatible with the maps from the stages.
* `AlgebraicGeometry.FormalSpace.isCofinalTower_of_idealSheafData`: a tower of closed subschemes of
  a locally Noetherian scheme squeezed between the powers of an ideal sheaf `J` is cofinal for
  `(X, |J|)`.
* `AlgebraicGeometry.FormalSpace.isCofinalTower_of_specMap_quotient_pow`: the tower
  `Spec (A ⧸ I ^ (n + 1))` is cofinal for `(Spec A, V(I))`, `A` Noetherian.
* `AlgebraicGeometry.FormalSpace.isCofinalTower_of_isPullback`: base change of a cofinal tower
  along `p : X ⟶ Z` is cofinal for `(X, p⁻¹ T)`.

## Implementation notes

The sections factoring through some stage form a subfunctor `P` of the subfunctor `Q` defining
the completion, and the inclusion `P ⊆ Q` is a local isomorphism: it is injective, and it is
locally surjective because the affine objects of the site form a dense subsite and over an affine
object `P` and `Q` agree, which is the cofinality condition. This is the argument of
`AlgebraicGeometry.Space.isIso_completionSubspaceComparison` (Stacks 0H8N).

The subfunctor `P` itself only depends on the tower: a section `h ≫ ι n` is sent to `h ≫ ι' n`.
That is well defined because the `ι n` are monomorphisms compatible with the transition maps, so
two factorizations through stages `n ≤ m` differ by the transition `Y n ⟶ Y m`.

## References

* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Supported sections of a represented presheaf -/

/-- A section `g : U ⟶ X` of the presheaf represented by an object `X` of the site is supported
in a set `T` of points of the underlying scheme of `X` exactly when every point of `U` maps into
`T`. -/
theorem hasImageIn_supportedPoints_iff_forall_mem {X : BigFppfOver B S hS}
    (T : Set ((BigFppfOver.toScheme B S hS).obj X)) (U : BigFppfOver B S hS) (g : U ⟶ X) :
    Space.HasImageIn B S hS (yoneda.obj X) (supportedPoints B S hS X T) U g ↔
      ∀ x, (BigFppfOver.toScheme B S hS).map g x ∈ T := by
  have key (p : Space.FieldValuedPoint B S hS (yoneda.obj U)) :
      Space.pointsToScheme B S hS X
          ((Space.FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map g) p).class
            B S hS (yoneda.obj X)) =
        (BigFppfOver.toScheme B S hS).map g (Space.schemePoint B S hS U p) := by
    rw [← Space.pointsMap_class, Space.pointsToScheme_pointsMap]
    rfl
  constructor
  · intro hg x
    have hx := hg (Space.schemePointRepresentative B S hS U x)
    change Space.pointsToScheme B S hS X
      ((Space.FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map g)
        (Space.schemePointRepresentative B S hS U x)).class B S hS (yoneda.obj X)) ∈ T at hx
    rwa [key, Space.schemePointRepresentative_point] at hx
  · intro h p
    change Space.pointsToScheme B S hS X
      ((Space.FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map g) p).class
        B S hS (yoneda.obj X)) ∈ T
    rw [key]
    exact h _

/-! ### Subfunctors agreeing over affine objects -/

/-- Let `P ≤ Q` be subfunctors of a presheaf on the big fppf site of `S`. If every section of `Q`
over an affine object of the site is a section of `P`, the sheafified inclusion `P ⟶ Q` is an
isomorphism: the inclusion is injective, and it is locally surjective because the affine objects
form a dense subsite (Stacks 021V). -/
theorem isIso_plusPlusSheaf_map_homOfLe_of_isAffine
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {P Q : Subfunctor F} (hle : P ≤ Q)
    (H : ∀ U : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ s ∈ Q.obj (op U), s ∈ P.obj (op U)) :
    IsIso ((plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
      (Subfunctor.homOfLe hle)) := by
  have hcd : (BigAffineFppf.inclusion B S hS).IsCoverDense
      (BigFppfOver.topology B S hS) :=
    Functor.IsDenseSubsite.isCoverDense (BigAffineFppf.topology B S hS)
      (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
  have hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Subfunctor.homOfLe hle) := by
    constructor
    intro U s
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (Functor.is_cover_of_isCoverDense (BigAffineFppf.inclusion B S hS) _ U)
    rintro V k ⟨⟨W₀, lift, map₀, hfac⟩⟩
    have hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj W₀)) :=
      BigAffineFppf.isAffine_toScheme_obj B S hS W₀
    set t₀ := Q.toFunctor.map map₀.op s
    have hmem : t₀.1 ∈ P.obj (op ((BigAffineFppf.inclusion B S hS).obj W₀)) :=
      H _ hW t₀.1 t₀.2
    refine ⟨⟨_, P.map lift.op hmem⟩, ?_⟩
    apply Subtype.ext
    change F.map lift.op (F.map map₀.op s.1) = _
    rw [← Functor.map_comp_apply, ← op_comp, hfac]
    rfl
  have hinj : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      (Subfunctor.homOfLe hle) :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_fac (BigFppfOver.topology B S hS)
      (Subfunctor.homOfLe_ι hle)
  have hfac := (BigFppfOver.topology B S hS).toSheafify_naturality (Subfunctor.homOfLe hle)
  have hsurj' : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      ((BigFppfOver.topology B S hS).sheafifyMap (Subfunctor.homOfLe hle)) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac
      (BigFppfOver.topology B S hS) hfac.symm
  have hinj' : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      ((BigFppfOver.topology B S hS).sheafifyMap (Subfunctor.homOfLe hle)) :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      (BigFppfOver.topology B S hS) _ hfac.symm
  exact (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hinj', hsurj'⟩

/-! ### Towers and their subfunctors -/

section Tower

variable {Y : ℕ → BigFppfOver B S hS} (t : ∀ n, Y n ⟶ Y (n + 1))

/-- A family `ι n : Y n ⟶ X` compatible with the transition maps `t n : Y n ⟶ Y (n + 1)` is
compatible with the composite transitions `Y n ⟶ Y (n + k)`; two such families at once. -/
theorem exists_tower_transition {X X' : BigFppfOver B S hS} (ι : ∀ n, Y n ⟶ X)
    (ι' : ∀ n, Y n ⟶ X') (hι : ∀ n, t n ≫ ι (n + 1) = ι n) (hι' : ∀ n, t n ≫ ι' (n + 1) = ι' n)
    (n k : ℕ) : ∃ T : Y n ⟶ Y (n + k), T ≫ ι (n + k) = ι n ∧ T ≫ ι' (n + k) = ι' n := by
  induction k with
  | zero => exact ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩
  | succ k ih =>
    obtain ⟨T, h₁, h₂⟩ := ih
    exact ⟨T ≫ t (n + k), (Category.assoc _ _ _).trans ((congrArg _ (hι (n + k))).trans h₁),
      (Category.assoc _ _ _).trans ((congrArg _ (hι' (n + k))).trans h₂)⟩

/-- Let `ι` be a family of monomorphisms out of the stages of a tower and `ι'` a second family,
both compatible with the transition maps. Two factorizations `h ≫ ι n = h' ≫ ι m` of a morphism
through stages give the same morphism `h ≫ ι' n = h' ≫ ι' m`. -/
theorem tower_comp_eq_of_comp_eq {X X' : BigFppfOver B S hS} {ι : ∀ n, Y n ⟶ X}
    {ι' : ∀ n, Y n ⟶ X'} (hmono : ∀ n, Mono (ι n)) (hι : ∀ n, t n ≫ ι (n + 1) = ι n)
    (hι' : ∀ n, t n ≫ ι' (n + 1) = ι' n) {U : BigFppfOver B S hS} {n m : ℕ} (h : U ⟶ Y n)
    (h' : U ⟶ Y m) (H : h ≫ ι n = h' ≫ ι m) : h ≫ ι' n = h' ≫ ι' m := by
  wlog hnm : n ≤ m generalizing n m
  · exact (this h' h H.symm ((le_total n m).resolve_left hnm)).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  obtain ⟨T, h₁, h₂⟩ := exists_tower_transition t ι ι' hι hι' n k
  have hT : h ≫ T = h' := (hmono (n + k)).right_cancellation _ _ (by rw [Category.assoc, h₁, H])
  rw [← hT, Category.assoc, h₂]

variable {X : BigFppfOver B S hS}

/-- The subfunctor of the presheaf represented by `X`, universe-lifted, of the sections that
factor through some stage `ι n : Y n ⟶ X` of a tower. -/
def towerSubfunctor (ι : ∀ n, Y n ⟶ X) : Subfunctor (yoneda.obj X ⋙ uliftFunctor.{u + 1}) where
  obj U := {f | ∃ n, ∃ h : U.unop ⟶ Y n, h ≫ ι n = f.down}
  map {U V} i f := by
    rintro ⟨n, h, hh⟩
    exact ⟨n, i.unop ≫ h, by rw [Category.assoc, hh]; rfl⟩

/-- A *cofinal tower* for an object `X` of the site and a set `T` of points of its underlying
scheme: compatible monomorphisms `ι n : Y n ⟶ X` from the stages of a tower
`t n : Y n ⟶ Y (n + 1)`, landing in `T`, such that every morphism from an affine object of the
site into `X` with image in `T` factors through some `ι n`. -/
structure IsCofinalTower (ι : ∀ n, Y n ⟶ X) (T : Set ((BigFppfOver.toScheme B S hS).obj X)) :
    Prop where
  /-- Each stage is a monomorphism of schemes into `X`. -/
  mono_toScheme (n : ℕ) : Mono ((BigFppfOver.toScheme B S hS).map (ι n))
  /-- The stages are compatible with the transition maps. -/
  comm (n : ℕ) : t n ≫ ι (n + 1) = ι n
  /-- Each stage lands in `T`. -/
  mem (n : ℕ) (y : (BigFppfOver.toScheme B S hS).obj (Y n)) :
    (BigFppfOver.toScheme B S hS).map (ι n) y ∈ T
  /-- A morphism from an affine object into `X` with image in `T` factors through some stage. -/
  exists_lift (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (g : V ⟶ X) (hg : ∀ x, (BigFppfOver.toScheme B S hS).map g x ∈ T) :
    ∃ n, ∃ h : V ⟶ Y n, h ≫ ι n = g

/-- The stages of a cofinal tower are monomorphisms of the site. -/
theorem IsCofinalTower.mono {ι : ∀ n, Y n ⟶ X} {T : Set ((BigFppfOver.toScheme B S hS).obj X)}
    (hT : IsCofinalTower t ι T) (n : ℕ) : Mono (ι n) :=
  (BigFppfOver.toScheme B S hS).mono_of_mono_map (hT.mono_toScheme n)

/-- A morphism of schemes into a stage, lifting a morphism of the site along the stage, is a
morphism of the site: it is automatically compatible with the structure morphisms to `S`. -/
theorem exists_hom_comp_eq_of_toScheme {V Y' X'' : BigFppfOver B S hS} (ι₀ : Y' ⟶ X'')
    (g : V ⟶ X'') (h : (BigFppfOver.toScheme B S hS).obj V ⟶ (BigFppfOver.toScheme B S hS).obj Y')
    (hh : h ≫ (BigFppfOver.toScheme B S hS).map ι₀ = (BigFppfOver.toScheme B S hS).map g) :
    ∃ h' : V ⟶ Y', h' ≫ ι₀ = g := by
  refine ⟨Over.homMk (ObjectProperty.homMk h) ?_, ?_⟩
  · rw [← Over.w ι₀, ← Category.assoc, ← Over.w g]
    congr 1
    apply ObjectProperty.hom_ext
    exact hh
  · apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp]
    exact hh

/-- The sections factoring through a stage landing in `T` are supported in `T`. -/
theorem towerSubfunctor_le {ι : ∀ n, Y n ⟶ X} {T : Set ((BigFppfOver.toScheme B S hS).obj X)}
    (hmem : ∀ n y, (BigFppfOver.toScheme B S hS).map (ι n) y ∈ T) :
    towerSubfunctor ι ≤
      Space.completionSubfunctor B S hS (yoneda.obj X) (supportedPoints B S hS X T) := by
  rintro U f ⟨n, h, hh⟩
  change Space.HasImageIn B S hS (yoneda.obj X) _ U.unop f.down
  rw [hasImageIn_supportedPoints_iff_forall_mem, ← hh]
  intro x
  rw [Functor.map_comp, Scheme.Hom.comp_apply]
  exact hmem n _

/-- The fppf sheafification of the tower subfunctor. -/
abbrev towerSheaf (ι : ∀ n, Y n ⟶ X) : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)) :=
  ⟨(BigFppfOver.topology B S hS).sheafify (towerSubfunctor ι).toFunctor,
    (BigFppfOver.topology B S hS).sheafify_isSheaf _⟩

/-- The sheafified inclusion of the tower subfunctor into the completion `X_{/T}`. -/
def towerSheafToCompletion {ι : ∀ n, Y n ⟶ X} {T : Set ((BigFppfOver.toScheme B S hS).obj X)}
    (hmem : ∀ n y, (BigFppfOver.toScheme B S hS).map (ι n) y ∈ T) :
    towerSheaf ι ⟶ Space.completionSheaf B S hS (yoneda.obj X) (supportedPoints B S hS X T) :=
  ObjectProperty.homMk
    ((BigFppfOver.topology B S hS).sheafifyMap (Subfunctor.homOfLe (towerSubfunctor_le hmem)))

/-- **The completion is the sheafified tower subfunctor.** For a cofinal tower of `(X, T)`, the
sheafified inclusion of the sections factoring through a stage into the completion `X_{/T}` is an
isomorphism. -/
theorem isIso_towerSheafToCompletion {ι : ∀ n, Y n ⟶ X}
    {T : Set ((BigFppfOver.toScheme B S hS).obj X)} (hT : IsCofinalTower t ι T) :
    IsIso (towerSheafToCompletion hT.mem) := by
  refine isIso_plusPlusSheaf_map_homOfLe_of_isAffine _ fun U hU s hs => ?_
  have hs' : Space.HasImageIn B S hS (yoneda.obj X) (supportedPoints B S hS X T) U s.down := hs
  rw [hasImageIn_supportedPoints_iff_forall_mem] at hs'
  exact hT.exists_lift U hU s.down hs'

/-- **A tower of thickenings cut out by powers of an ideal sheaf is cofinal.** Let the underlying
scheme of `X` be locally Noetherian and `J` an ideal sheaf on it. A tower of monomorphisms
`ι n : Y n ⟶ X` landing in the support of `J`, such that every closed subscheme `V(J ^ k)`
factors through some stage, is a cofinal tower for `(X, |J|)`. -/
theorem isCofinalTower_of_idealSheafData
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj X)]
    (J : ((BigFppfOver.toScheme B S hS).obj X).IdealSheafData) {ι : ∀ n, Y n ⟶ X}
    (hmono : ∀ n, Mono ((BigFppfOver.toScheme B S hS).map (ι n)))
    (hcomm : ∀ n, t n ≫ ι (n + 1) = ι n)
    (hsupp : ∀ n y, (BigFppfOver.toScheme B S hS).map (ι n) y ∈ J.support)
    (hcof : ∀ k, ∃ n, ∃ h : (J ^ k).subscheme ⟶ (BigFppfOver.toScheme B S hS).obj (Y n),
      h ≫ (BigFppfOver.toScheme B S hS).map (ι n) = (J ^ k).subschemeι) :
    IsCofinalTower t ι (J.support : Set ((BigFppfOver.toScheme B S hS).obj X)) where
  mono_toScheme := hmono
  comm := hcomm
  mem := hsupp
  exists_lift V hV g hg := by
    obtain ⟨k, h₀, hh₀⟩ := Scheme.Hom.exists_lift_subschemeι_pow_of_range_subset_support
      ((BigFppfOver.toScheme B S hS).map g) J (by rintro _ ⟨x, rfl⟩; exact hg x)
    obtain ⟨n, h₁, hh₁⟩ := hcof k
    exact ⟨n, exists_hom_comp_eq_of_toScheme (ι n) g (h₀ ≫ h₁)
      (by rw [Category.assoc, hh₁, hh₀])⟩

/-- **The base change of a cofinal tower is cofinal.** Let `p : X ⟶ Z` be a morphism of the site
and `(Y₀, ι₀)` a cofinal tower for `(Z, T₀)`. A tower `Y` over `X` whose stages are, on underlying
schemes, the base changes `Y n = X ×_Z Y₀ n` is a cofinal tower for `(X, p⁻¹ T₀)`. -/
theorem isCofinalTower_of_isPullback {Z : BigFppfOver B S hS} (p : X ⟶ Z)
    {T₀ : Set ((BigFppfOver.toScheme B S hS).obj Z)} {Y₀ : ℕ → BigFppfOver B S hS}
    {t₀ : ∀ n, Y₀ n ⟶ Y₀ (n + 1)} {ι₀ : ∀ n, Y₀ n ⟶ Z} (h₀ : IsCofinalTower t₀ ι₀ T₀)
    {ι : ∀ n, Y n ⟶ X} (q : ∀ n, Y n ⟶ Y₀ n) (hcomm : ∀ n, t n ≫ ι (n + 1) = ι n)
    (hpb : ∀ n, IsPullback ((BigFppfOver.toScheme B S hS).map (ι n))
      ((BigFppfOver.toScheme B S hS).map (q n)) ((BigFppfOver.toScheme B S hS).map p)
      ((BigFppfOver.toScheme B S hS).map (ι₀ n))) :
    IsCofinalTower t ι ((BigFppfOver.toScheme B S hS).map p ⁻¹' T₀) where
  mono_toScheme n := by
    have := h₀.mono_toScheme n
    refine ⟨fun a b hab => (hpb n).hom_ext hab ?_⟩
    rw [← cancel_mono ((BigFppfOver.toScheme B S hS).map (ι₀ n)), Category.assoc,
      Category.assoc, ← (hpb n).w, ← Category.assoc, hab, Category.assoc]
  comm := hcomm
  mem n y := by
    change ((BigFppfOver.toScheme B S hS).map p) ((BigFppfOver.toScheme B S hS).map (ι n) y) ∈ T₀
    rw [← Scheme.Hom.comp_apply, (hpb n).w, Scheme.Hom.comp_apply]
    exact h₀.mem n _
  exists_lift V hV g hg := by
    obtain ⟨n, h, hh⟩ := h₀.exists_lift V hV (g ≫ p) (fun x => by
      rw [Functor.map_comp, Scheme.Hom.comp_apply]
      exact hg x)
    refine ⟨n, exists_hom_comp_eq_of_toScheme (ι n) g ((hpb n).lift
      ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map h) ?_) ?_⟩
    · rw [← Functor.map_comp, ← Functor.map_comp, hh]
    · exact (hpb n).lift_fst _ _ _

/-- **The tower `Spec (A ⧸ I ^ (n + 1))` is cofinal in `Spec A`.** Let `Z` be an object of the
site with underlying scheme identified with `Spec A`, `A` Noetherian, and `I ⊆ A` an ideal. A tower
whose stages are, compatibly with that identification, the closed immersions
`Spec (A ⧸ I ^ (n + 1)) ⟶ Spec A` is a cofinal tower for `(Z, V(I))`. -/
theorem isCofinalTower_of_specMap_quotient_pow {A : CommRingCat.{u}} [IsNoetherianRing A]
    (eX : (BigFppfOver.toScheme B S hS).obj X ≅ Spec A) (I : Ideal A) {ι : ∀ n, Y n ⟶ X}
    (hY : ∀ n, ∃ e : (BigFppfOver.toScheme B S hS).obj (Y n) ≅ Spec (.of (A ⧸ I ^ (n + 1))),
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ eX.inv =
        (BigFppfOver.toScheme B S hS).map (ι n))
    (hcomm : ∀ n, t n ≫ ι (n + 1) = ι n) :
    IsCofinalTower t ι (eX.hom ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) where
  mono_toScheme n := by
    obtain ⟨e, he⟩ := hY n
    rw [← he]
    infer_instance
  comm := hcomm
  mem n y := by
    obtain ⟨e, he⟩ := hY n
    change eX.hom ((BigFppfOver.toScheme B S hS).map (ι n) y) ∈ PrimeSpectrum.zeroLocus (I : Set A)
    rw [← he, ← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Scheme.Hom.comp_apply]
    intro a ha
    change Ideal.Quotient.mk (I ^ (n + 1)) a ∈ (e.hom y).asIdeal
    apply (e.hom y).isPrime.mem_of_pow_mem (n + 1)
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow ha _)]
    exact Ideal.zero_mem _
  exists_lift V hV g hg := by
    obtain ⟨n, ℓ, hℓ⟩ := Scheme.Hom.exists_lift_specMap_quotient_pow I
      ((BigFppfOver.toScheme B S hS).map g ≫ eX.hom) hg
    obtain ⟨e, he⟩ := hY n
    refine ⟨n, exists_hom_comp_eq_of_toScheme (ι n) g (ℓ ≫ e.inv) ?_⟩
    simp only [← he, Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hℓ, Iso.hom_inv_id,
      Category.comp_id]
    rfl

end Tower

/-! ### Comparing two embeddings of one tower -/

section Comparison

variable {Y : ℕ → BigFppfOver B S hS} {t : ∀ n, Y n ⟶ Y (n + 1)} {X X' : BigFppfOver B S hS}
  {ι : ∀ n, Y n ⟶ X} {ι' : ∀ n, Y n ⟶ X'}

/-- A chosen stage through which a section of the tower subfunctor factors. -/
def towerIndex {U : (BigFppfOver B S hS)ᵒᵖ} (f : (towerSubfunctor ι).toFunctor.obj U) : ℕ :=
  f.2.choose

/-- A chosen factorization of a section of the tower subfunctor through the stage
`towerIndex f`. -/
def towerLift {U : (BigFppfOver B S hS)ᵒᵖ} (f : (towerSubfunctor ι).toFunctor.obj U) :
    U.unop ⟶ Y (towerIndex f) :=
  f.2.choose_spec.choose

/-- The chosen factorization is a factorization. -/
theorem towerLift_comp {U : (BigFppfOver B S hS)ᵒᵖ} (f : (towerSubfunctor ι).toFunctor.obj U) :
    towerLift f ≫ ι (towerIndex f) = f.1.down :=
  f.2.choose_spec.choose_spec

/-- The morphism of tower subfunctors sending a section `h ≫ ι n` of `X` to the section
`h ≫ ι' n` of `X'`; it is well defined by `tower_comp_eq_of_comp_eq`. -/
def towerSubfunctorMap (hmono : ∀ n, Mono (ι n)) (hι : ∀ n, t n ≫ ι (n + 1) = ι n)
    (hι' : ∀ n, t n ≫ ι' (n + 1) = ι' n) :
    (towerSubfunctor ι).toFunctor ⟶ (towerSubfunctor ι').toFunctor where
  app U := ↾fun f => ⟨ULift.up (towerLift f ≫ ι' (towerIndex f)), towerIndex f, towerLift f, rfl⟩
  naturality U V i := by
    ext f
    apply Subtype.ext
    apply ULift.ext
    have key := tower_comp_eq_of_comp_eq t hmono hι hι'
      (towerLift ((towerSubfunctor ι).toFunctor.map i f)) (i.unop ≫ towerLift f)
      (by rw [towerLift_comp, Category.assoc, towerLift_comp]; rfl)
    exact key.trans (Category.assoc _ _ _)

/-- The morphism of tower subfunctors sends a section with a factorization `h ≫ ι n` to
`h ≫ ι' n`. -/
theorem towerSubfunctorMap_app_down (hmono : ∀ n, Mono (ι n)) (hι : ∀ n, t n ≫ ι (n + 1) = ι n)
    (hι' : ∀ n, t n ≫ ι' (n + 1) = ι' n) {U : (BigFppfOver B S hS)ᵒᵖ}
    (f : (towerSubfunctor ι).toFunctor.obj U) {n : ℕ} (h : U.unop ⟶ Y n)
    (hh : h ≫ ι n = f.1.down) :
    ((towerSubfunctorMap hmono hι hι').app U f).1.down = h ≫ ι' n :=
  tower_comp_eq_of_comp_eq t hmono hι hι' _ _ ((towerLift_comp f).trans hh.symm)

/-- **One tower, two embeddings.** For two families of monomorphisms out of the stages of one
tower, both compatible with the transition maps, the subfunctors of sections factoring through a
stage are isomorphic. -/
def towerSubfunctorIso (hmono : ∀ n, Mono (ι n)) (hmono' : ∀ n, Mono (ι' n))
    (hι : ∀ n, t n ≫ ι (n + 1) = ι n) (hι' : ∀ n, t n ≫ ι' (n + 1) = ι' n) :
    (towerSubfunctor ι).toFunctor ≅ (towerSubfunctor ι').toFunctor where
  hom := towerSubfunctorMap hmono hι hι'
  inv := towerSubfunctorMap hmono' hι' hι
  hom_inv_id := by
    ext U f
    apply Subtype.ext
    apply ULift.ext
    obtain ⟨n, h, hh⟩ := f.2
    have h₁ := towerSubfunctorMap_app_down hmono hι hι' f h hh
    exact (towerSubfunctorMap_app_down hmono' hι' hι _ h h₁.symm).trans hh
  inv_hom_id := by
    ext U f
    apply Subtype.ext
    apply ULift.ext
    obtain ⟨n, h, hh⟩ := f.2
    have h₁ := towerSubfunctorMap_app_down hmono' hι' hι f h hh
    exact (towerSubfunctorMap_app_down hmono hι hι' _ h h₁.symm).trans hh

/-- The sheafified isomorphism of tower subfunctors. -/
def towerSheafIso (hmono : ∀ n, Mono (ι n)) (hmono' : ∀ n, Mono (ι' n))
    (hι : ∀ n, t n ≫ ι (n + 1) = ι n) (hι' : ∀ n, t n ≫ ι' (n + 1) = ι' n) :
    towerSheaf ι ≅ towerSheaf ι' where
  hom := ObjectProperty.homMk ((BigFppfOver.topology B S hS).sheafifyMap
    (towerSubfunctorIso hmono hmono' hι hι').hom)
  inv := ObjectProperty.homMk ((BigFppfOver.topology B S hS).sheafifyMap
    (towerSubfunctorIso hmono hmono' hι hι').inv)
  hom_inv_id := by
    apply Sheaf.hom_ext
    change (BigFppfOver.topology B S hS).sheafifyMap _ ≫
      (BigFppfOver.topology B S hS).sheafifyMap _ = 𝟙 _
    rw [← GrothendieckTopology.sheafifyMap_comp, Iso.hom_inv_id,
      GrothendieckTopology.sheafifyMap_id]
  inv_hom_id := by
    apply Sheaf.hom_ext
    change (BigFppfOver.topology B S hS).sheafifyMap _ ≫
      (BigFppfOver.topology B S hS).sheafifyMap _ = 𝟙 _
    rw [← GrothendieckTopology.sheafifyMap_comp, Iso.inv_hom_id,
      GrothendieckTopology.sheafifyMap_id]

variable {T : Set ((BigFppfOver.toScheme B S hS).obj X)}
  {T' : Set ((BigFppfOver.toScheme B S hS).obj X')}

/-- **Completions along a common cofinal tower agree.** If one tower `Y` embeds as a cofinal
tower into `(X, T)` and into `(X', T')`, the completions `X_{/T}` and `X'_{/T'}` are isomorphic:
both are the sheafified subfunctor of sections factoring through a stage, and those subfunctors
are isomorphic. -/
def completionSheafIsoOfCofinalTower (hT : IsCofinalTower t ι T) (hT' : IsCofinalTower t ι' T') :
    Space.completionSheaf B S hS (yoneda.obj X) (supportedPoints B S hS X T) ≅
      Space.completionSheaf B S hS (yoneda.obj X') (supportedPoints B S hS X' T') :=
  haveI := isIso_towerSheafToCompletion t hT
  haveI := isIso_towerSheafToCompletion t hT'
  (asIso (towerSheafToCompletion hT.mem)).symm ≪≫
    towerSheafIso hT.mono hT'.mono hT.comm hT'.comm ≪≫
    asIso (towerSheafToCompletion hT'.mem)

/-- The section of the tower subfunctor given by a morphism into a stage. -/
def towerStageToTower (ι : ∀ n, Y n ⟶ X) (n : ℕ) :
    yoneda.obj (Y n) ⋙ uliftFunctor.{u + 1} ⟶ (towerSubfunctor ι).toFunctor where
  app U := ↾fun h => ⟨ULift.up (h.down ≫ ι n), n, h.down, rfl⟩
  naturality U V i := by
    ext h
    apply Subtype.ext
    apply ULift.ext
    exact Category.assoc _ _ _

/-- The morphism from the presheaf represented by the stage `Y n` into the completion `X_{/T}`
(sheafified), induced by `ι n : Y n ⟶ X`. -/
def towerStageToCompletion (hmem : ∀ n y, (BigFppfOver.toScheme B S hS).map (ι n) y ∈ T)
    (n : ℕ) : yoneda.obj (Y n) ⋙ uliftFunctor.{u + 1} ⟶
      (Space.completionSheaf B S hS (yoneda.obj X) (supportedPoints B S hS X T)).obj :=
  towerStageToTower ι n ≫ Subfunctor.homOfLe (towerSubfunctor_le hmem) ≫
    (BigFppfOver.topology B S hS).toSheafify _

/-- The stage map into the completion factors through the sheafified tower subfunctor. -/
theorem towerStageToCompletion_eq (hmem : ∀ n y, (BigFppfOver.toScheme B S hS).map (ι n) y ∈ T)
    (n : ℕ) : towerStageToCompletion hmem n =
      towerStageToTower ι n ≫ (BigFppfOver.topology B S hS).toSheafify _ ≫
        (towerSheafToCompletion hmem).hom := by
  exact congrArg (towerStageToTower ι n ≫ ·)
    ((BigFppfOver.topology B S hS).toSheafify_naturality
      (Subfunctor.homOfLe (towerSubfunctor_le hmem)))

/-- The isomorphism of tower subfunctors carries the section given by a morphism into a stage
to the section given by the same morphism. -/
theorem towerStageToTower_comp_towerSubfunctorIso_hom (hmono : ∀ n, Mono (ι n))
    (hmono' : ∀ n, Mono (ι' n)) (hι : ∀ n, t n ≫ ι (n + 1) = ι n)
    (hι' : ∀ n, t n ≫ ι' (n + 1) = ι' n) (n : ℕ) :
    towerStageToTower ι n ≫ (towerSubfunctorIso hmono hmono' hι hι').hom =
      towerStageToTower ι' n := by
  ext U h
  apply Subtype.ext
  apply ULift.ext
  exact towerSubfunctorMap_app_down hmono hι hι' _ h.down rfl

/-- The isomorphism of completions, preceded by the sheafified tower subfunctor of `X`, is the
sheafified isomorphism of tower subfunctors followed by the one of `X'`. -/
theorem towerSheafToCompletion_comp_completionSheafIsoOfCofinalTower_hom
    (hT : IsCofinalTower t ι T) (hT' : IsCofinalTower t ι' T') :
    towerSheafToCompletion hT.mem ≫ (completionSheafIsoOfCofinalTower hT hT').hom =
      (towerSheafIso hT.mono hT'.mono hT.comm hT'.comm).hom ≫
        towerSheafToCompletion hT'.mem := by
  have := isIso_towerSheafToCompletion t hT
  simp only [completionSheafIsoOfCofinalTower, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    asIso_hom, IsIso.hom_inv_id_assoc]

/-- **Compatibility with the stages.** The isomorphism of completions induced by a common cofinal
tower carries the map from each stage `Y n` into `X_{/T}` to the map from `Y n` into
`X'_{/T'}`. -/
theorem towerStageToCompletion_comp_completionSheafIsoOfCofinalTower_hom
    (hT : IsCofinalTower t ι T) (hT' : IsCofinalTower t ι' T') (n : ℕ) :
    towerStageToCompletion hT.mem n ≫ (completionSheafIsoOfCofinalTower hT hT').hom.hom =
      towerStageToCompletion hT'.mem n := by
  have h₂ := congrArg (fun φ => towerStageToTower ι n ≫
    (BigFppfOver.topology B S hS).toSheafify (towerSubfunctor ι).toFunctor ≫ φ.hom)
    (towerSheafToCompletion_comp_completionSheafIsoOfCofinalTower_hom hT hT')
  have h₃ := (reassoc_of% ((BigFppfOver.topology B S hS).toSheafify_naturality
    (towerSubfunctorIso hT.mono hT'.mono hT.comm hT'.comm).hom))
    (towerSheafToCompletion hT'.mem).hom
  simp only [ObjectProperty.FullSubcategory.comp_hom] at h₂
  rw [towerStageToCompletion_eq, towerStageToCompletion_eq,
    ← towerStageToTower_comp_towerSubfunctorIso_hom hT.mono hT'.mono hT.comm hT'.comm n]
  simp only [Category.assoc]
  rw [h₂]
  congr 1
  exact h₃.symm

end Comparison

end AlgebraicGeometry.FormalSpace

end
