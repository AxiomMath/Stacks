module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteTypeII.ModuleFlatLocusFiniteType
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.FlatFibreSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Surjective
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative associated points in the nearby fibres

Let `f : X ⟶ S` be a morphism of schemes locally of finite type, let `F` be a quasi-coherent
`𝒪_X`-module of finite type and let `ξ` be a point of the relative assassin `Ass_{X/S}(F)`. The
closure `Z` of `ξ` then contains a nonempty open `V` with the property that for every `s` in the
image `f(V)` the generic points of the fibre `V_s` lie again in `Ass_{X/S}(F)`.

Consequently, for a finite type morphism `f : X ⟶ Y` onto an irreducible scheme with generic
point `η` and an open `U ⊆ X`, failure of the associated points of `F` on the generic fibre to be
contained in `U` propagates: the associated points on the fibre over `y` fail to be contained in
`U` for every `y` in some nonempty open of `Y`.

## Main results

* `Stacks.RelativeAssassin.exists_open_closure_genericPoints_fibre_mem_relativeAssassin`
* `Stacks.RelativeAssassin.exists_open_forall_not_associatedPoints_fibre_subset`

## Implementation notes

For the first result the base is replaced by the reduced closed subscheme `T` supported on the
closure of `f ξ`, which is integral and has `f ξ` for its generic point. Membership in the
relative assassin is unchanged by this base change, since `T ⟶ S` is a closed immersion and
hence locally quasi-finite. Over `T` the point `ξ` lies above a generic point, so the local ring
of the base there is a field and `F` is automatically flat over `T` at `ξ`; as the relative flat
locus of a finite type module under a locally finite type morphism is open, flatness then holds
on a whole open neighbourhood `U` of `ξ`, and `V` is the part of the closure of `ξ` inside `U`.
A generic point of `V_s` is a generic point of an irreducible component of the fibre over `s` of
the reduced closed subscheme supported on the closure of `ξ`, so the criterion for a point at
which the module is flat to be a relative associated point applies to it.

The second result is proved by an argument that deliberately departs from the one given in the
source. There the hypothesis that `Ass_{X_η}(F_η)` is not contained in `U_η` is used to assert
that the closure of the chosen associated point meets `U_η` in the empty set, which does not
follow: failure of containment produces a single point outside `U_η`, not disjointness. The
conclusion reached there is moreover the containment of the fibrewise associated points in `U`,
which is the assertion of Tag 05KP and not the one proved here. The proof below instead observes
that a point `ξ` of `Ass_{X_η}(F_η)` outside `U_η` lies outside the open set `U` as a point of
`X`, so a point of the closure of `ξ` belonging to `U` would exhibit `U` as an open neighbourhood
of a specialization of `ξ` and hence force `ξ ∈ U`; the closure of `ξ` is therefore disjoint from
`U` outright, with no shrinking. The first result applied to `ξ` yields a nonempty open `V` of
that closure whose fibrewise generic points lie in `Ass_{X/Y}(F)`, and they avoid `U` because
they lie in the closure of `ξ`. That those generic points exist over a nonempty open of `Y` is
Tag 05F5, applied to an affine chart of `V` above an affine chart of `Y` around `η`; over an
affine base the restricted morphism is affine and hence quasi-compact, as that tag requires.

## References

* [Stacks Project, Tag 05F1](https://stacks.math.columbia.edu/tag/05F1)
* [Stacks Project, Tag 05KN](https://stacks.math.columbia.edu/tag/05KN)
* [Stacks Project, Tag 05KP](https://stacks.math.columbia.edu/tag/05KP)
* [Stacks Project, Tag 05F5](https://stacks.math.columbia.edu/tag/05F5)
* [Stacks Project, Tag 0GSI](https://stacks.math.columbia.edu/tag/0GSI)
* [Stacks Project, Tag 05IQ](https://stacks.math.columbia.edu/tag/05IQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.RelativeAssassin

/-- The reduced closed subscheme structure on the closure of a point of a scheme. -/
private def reducedPointClosure {S : Scheme.{u}} (s : S) : S.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({s} : Set S))

/-- The image of the reduced closed subscheme supported on the closure of a point is that
closure. -/
private theorem range_subschemeι_reducedPointClosure {S : Scheme.{u}} (s : S) :
    Set.range (reducedPointClosure s).subschemeι = closure ({s} : Set S) := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  simp [reducedPointClosure]

/-- The reduced closed subscheme supported on the closure of a point is integral. -/
private theorem isIntegral_reducedPointClosure {S : Scheme.{u}} (s : S) :
    IsIntegral (reducedPointClosure s).subscheme := by
  have : IsReduced (reducedPointClosure s).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace (reducedPointClosure s).subscheme := by
    refine Scheme.IdealSheafData.irreducibleSpace_subscheme S _ ?_
    rw [range_subschemeι_reducedPointClosure]
    exact isIrreducible_singleton.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The point itself is the generic point of the reduced closed subscheme supported on its
closure. -/
private theorem exists_isGenericPoint_reducedPointClosure {S : Scheme.{u}} (s : S) :
    ∃ y : (reducedPointClosure s).subscheme,
      (reducedPointClosure s).subschemeι y = s ∧ IsGenericPoint y Set.univ := by
  obtain ⟨y, hy⟩ : s ∈ Set.range (reducedPointClosure s).subschemeι := by
    rw [range_subschemeι_reducedPointClosure]
    exact subset_closure rfl
  refine ⟨y, hy, isGenericPoint_def.mpr ?_⟩
  rw [(reducedPointClosure s).subschemeι.isEmbedding.closure_eq_preimage_closure_image,
    Set.image_singleton, hy]
  rw [← range_subschemeι_reducedPointClosure]
  simp

/-- An integral scheme has only finitely many weakly associated points, namely its generic
point. -/
private theorem schemeWeaklyAssociatedPoints_finite_of_isIntegral {Y : Scheme.{u}} [IsIntegral Y]
    (y : Y) : ∃ U : Y.Opens, y ∈ U ∧
      (Stacks.Divisors.schemeWeaklyAssociatedPoints Y ∩ (U : Set Y)).Finite := by
  refine ⟨⊤, Set.mem_univ y, ?_⟩
  rw [AlgebraicGeometry.weaklyAssociatedPointsOfScheme_eq_genericPoints,
    genericPoints_eq_singleton]
  simp

/-- Every module over a field is flat. The module structure is taken as an explicit argument so
that the statement applies to a module structure that is not the one found by instance search. -/
private theorem flat_of_isField {R M : Type*} [CommRing R] [AddCommGroup M]
    (inst : Module R M) (hR : IsField R) : @Module.Flat R M _ _ inst := by
  let : Module R M := inst
  let : Field R := hR.toField
  exact Module.Flat.of_free

/-- A module is flat over the base at a point whose image has a field for its local ring. -/
private theorem isFlatOverAt_of_isField_stalk {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (x : X) (hS : IsField (S.presheaf.stalk (f x))) :
    AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x :=
  flat_of_isField _ hS

/-- Over an integral base a finite type quasi-coherent module is flat on an open neighbourhood
of every point lying above a generic point. -/
private theorem exists_open_subset_flatLocus_of_isIntegral_base
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    [IsIntegral S] (x : X) (hx : f x ∈ genericPoints S) :
    ∃ U : X.Opens, x ∈ U ∧ (U : Set X) ⊆ AlgebraicGeometry.flatLocus f F := by
  have hopen : IsOpen (AlgebraicGeometry.flatLocus f F) :=
    AlgebraicGeometry.isOpen_flatLocus_of_locallyOfFiniteType f F
      schemeWeaklyAssociatedPoints_finite_of_isIntegral
  have hflat : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x :=
    isFlatOverAt_of_isField_stalk f F x
      (isField_stalk_of_closure_mem_irreducibleComponents S (f x) hx)
  obtain ⟨U, hU, hUopen, hxU⟩ := isOpen_iff_forall_mem_open.mp hopen x hflat
  exact ⟨⟨U, hUopen⟩, hxU, hU⟩

/-- A closed immersion identifies the closure of a point with the closure of its image. -/
private def closureHomeomorph {X X' : Scheme.{u}} (j : X' ⟶ X) [IsClosedImmersion j]
    (x' : X') (x : X) (hx : j x' = x) :
    closure ({x'} : Set X') ≃ₜ closure ({x} : Set X) := by
  have hpre : j ⁻¹' closure ({x} : Set X) = closure ({x'} : Set X') := by
    rw [← hx]
    simpa using
      (j.isClosedEmbedding.isEmbedding.closure_eq_preimage_closure_image ({x'} : Set X')).symm
  have hrange : closure ({x} : Set X) ⊆ Set.range j :=
    closure_minimal (Set.singleton_subset_iff.mpr ⟨x', hx⟩)
      j.isClosedEmbedding.isClosed_range
  exact (Homeomorph.setCongr hpre.symm).trans
    (j.isClosedEmbedding.isEmbedding.homeomorphOfSubsetRange hrange)

/-- A generalization of a generic point of an irreducible component is that point. -/
private theorem eq_of_specializes_mem_genericPoints {A : Type*} [TopologicalSpace A] [T0Space A]
    {a : A} (ha : a ∈ genericPoints A) {b : A} (hba : b ⤳ a) : b = a := by
  have hback : closure ({b} : Set A) ⊆ closure ({a} : Set A) :=
    (genericPoints.component ⟨a, ha⟩).2.2 isIrreducible_singleton.closure
      (specializes_iff_closure_subset.mp hba)
  exact (hba.antisymm (specializes_iff_closure_subset.mpr hback)).eq

/-- A point of a scheme is a generic point of an irreducible component as soon as every
generalization of it equals it. -/
private theorem mem_genericPoints_of_forall_specializes {A : Type*} [TopologicalSpace A]
    [T0Space A] [QuasiSober A] (a : A) (h : ∀ b : A, b ⤳ a → b = a) : a ∈ genericPoints A := by
  let Z : irreducibleComponents A :=
    ⟨irreducibleComponent a, irreducibleComponent_mem_irreducibleComponents a⟩
  have hηa : (genericPoints.ofComponent Z : A) ⤳ a :=
    (genericPoints.isGenericPoint_ofComponent Z).specializes mem_irreducibleComponent
  rw [← h _ hηa]
  exact (genericPoints.ofComponent Z).2

/-- A nonempty quasi-sober space has a generic point of an irreducible component. -/
private theorem genericPoints_nonempty {A : Type*} [TopologicalSpace A] [QuasiSober A]
    (a : A) : (genericPoints A).Nonempty :=
  ⟨(genericPoints.ofComponent
      ⟨irreducibleComponent a, irreducibleComponent_mem_irreducibleComponents a⟩).1,
    (genericPoints.ofComponent _).2⟩

/-- A point is a generic point of an irreducible component as soon as an injective continuous map
sends it to a generic point of a subspace containing the images of all its generalizations. -/
private theorem mem_genericPoints_of_injective {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [T0Space A] [QuasiSober A] [T0Space B] {E : Set B} {e : E}
    (he : e ∈ genericPoints E) {ψ : A → B} (hψ : Continuous ψ) (hψinj : Function.Injective ψ)
    {a : A} (ha : ψ a = e) (hE : ∀ z, z ⤳ a → ψ z ∈ E) : a ∈ genericPoints A := by
  refine mem_genericPoints_of_forall_specializes a fun z hz => hψinj ?_
  have hspec : (⟨ψ z, hE z hz⟩ : E) ⤳ e := by
    rw [subtype_specializes_iff, ← ha]
    exact hz.map hψ
  rw [ha]
  exact congrArg Subtype.val (eq_of_specializes_mem_genericPoints he hspec)

/-- The two projections of a fibre product of schemes agree after composing to the base. -/
private theorem pullback_condition_apply {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z : pullback (C := Scheme.{u}) f g) : f (pullback.fst f g z) = g (pullback.snd f g z) := by
  simpa [Scheme.Hom.comp_apply] using
    congrArg (fun k : pullback (C := Scheme.{u}) f g ⟶ S => k z)
      (Limits.pullback.condition (f := f) (g := g))

/-- Let `m : W ⟶ X` be injective, lying over an injective `i : T ⟶ S` through `g : W ⟶ T`. A point
of the fibre of `g` over `t` that `m` sends to a generic point of the part of the fibre of `f` over
`i t` lying in `E`, where `E` contains the images of all its generalizations, is a generic point of
the fibre of `g`. -/
private theorem mem_genericPoints_fiber_of_injective {W X T S : Scheme.{u}} (f : X ⟶ S)
    (g : W ⟶ T) (m : W ⟶ X) (i : T ⟶ S) (hm : Function.Injective m)
    (hcomm : ∀ w, f (m w) = i (g w)) (t : T) (s : S) (hs : i t = s) {E : Set X}
    (e : genericPoints (f.fiberι s ⁻¹' E : Set (f.fiber s))) (z₀ : g.fiber t)
    (hz₀ : m (g.fiberι t z₀) = f.fiberι s e.1.1) (hE : ∀ z, z ⤳ z₀ → m (g.fiberι t z) ∈ E) :
    z₀ ∈ genericPoints (g.fiber t) := by
  have hbase (z : g.fiber t) : f (m (g.fiberι t z)) = s := by
    rw [hcomm, g.apply_fiberι, hs]
  let ψ : g.fiber t → f.fiber s := fun z =>
    (f.fiberHomeo s).symm ⟨m (g.fiberι t z), hbase z⟩
  have hψι (z : g.fiber t) : f.fiberι s (ψ z) = m (g.fiberι t z) := by simp [ψ]
  have hψz₀ : ψ z₀ = e.1.1 := by
    apply (f.fiberι s).isEmbedding.injective
    rw [hψι, hz₀]
  refine mem_genericPoints_of_injective e.2 (ψ := ψ) (a := z₀) ?_ (fun z₁ z₂ h => ?_) hψz₀
    fun z hz => ?_
  · exact (f.fiberHomeo s).symm.continuous_toFun.comp
      (continuous_induced_rng.mpr (m.continuous.comp (g.fiberι t).continuous))
  · apply (g.fiberι t).isEmbedding.injective
    apply hm
    simpa only [hψι] using congrArg (f.fiberι s) h
  · change f.fiberι s (ψ z) ∈ E
    rw [hψι]
    exact hE z hz

/-- Let `i : T ⟶ S` be a closed immersion, `x'` a point of the relative assassin of the base
change of `F` to `T`, and `U` an open on which that base change is flat over `T`. The generic
points of the fibres of `f` restricted to the image of `U ∩ closure {x'}` in the closure of `ξ`
lie in the relative assassin of `F`. -/
private theorem fiberι_mem_relativeAssassin_of_subset_flatLocus {X S T : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (i : T ⟶ S) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x' : pullback (C := Scheme.{u}) f i)
    (hx' : x' ∈ Stacks.Divisors.relativeAssassin (pullback.snd f i)
      ((Scheme.Modules.pullback (pullback.fst f i)).obj F))
    (U : (pullback (C := Scheme.{u}) f i).Opens)
    (hU : (U : Set (pullback (C := Scheme.{u}) f i)) ⊆ AlgebraicGeometry.flatLocus
      (pullback.snd f i) ((Scheme.Modules.pullback (pullback.fst f i)).obj F))
    (ξ : X) (hξ : pullback.fst f i x' = ξ) (x : X)
    (η : genericPoints ((f.fiberι (f x)) ⁻¹' (Subtype.val ''
      (closureHomeomorph (pullback.fst f i) x' ξ hξ ''
        (Subtype.val ⁻¹' (U : Set (pullback (C := Scheme.{u}) f i))))) : Set (f.fiber (f x)))) :
    f.fiberι (f x) η.1.1 ∈ Stacks.Divisors.relativeAssassin f F := by
  let f' := pullback.snd f i
  let j := pullback.fst f i
  let F' := (Scheme.Modules.pullback j).obj F
  have : F'.IsQuasicoherent := isQuasicoherent_pullbackObj j F
  have : F'.IsFiniteType := by
    dsimp [F']
    exact AlgebraicGeometry.SheafOfModules.pullback_isFiniteType j.toLRSHom.toShHom F
  let e := closureHomeomorph j x' ξ hξ
  have hcond (z : pullback (C := Scheme.{u}) f i) : f (j z) = i (f' z) :=
    pullback_condition_apply f i z
  let k := (reducedPointClosure x').subschemeι
  let g := k ≫ f'
  have hk (y : (reducedPointClosure x').subscheme) : k y ∈ closure ({x'} : Set _) := by
    rw [← range_subschemeι_reducedPointClosure]
    exact ⟨y, rfl⟩
  obtain ⟨_, ⟨a, ha, rfl⟩, hpη⟩ := η.1.2
  have hpη' : j a.1 = f.fiberι (f x) η.1.1 := hpη
  let t := f' a.1
  have hbase : i t = f x :=
    (hcond a.1).symm.trans ((congrArg f hpη').trans (f.apply_fiberι _ _))
  obtain ⟨y, hy⟩ : a.1 ∈ Set.range k := by
    rw [range_subschemeι_reducedPointClosure]
    exact a.2
  have hgy : g y = t := congrArg f' hy
  obtain ⟨zη, hzη⟩ : y ∈ Set.range (g.fiberι t) :=
    (g.range_fiberι t).ge hgy
  let φ : g.fiber t → closure ({ξ} : Set X) := fun z => e ⟨k (g.fiberι t z), hk _⟩
  have hφ : Continuous φ := e.continuous_toFun.comp
    (continuous_induced_rng.mpr (k.continuous.comp (g.fiberι t).continuous))
  have hφa : e a = φ zη := congrArg e (Subtype.ext (hy.symm.trans (congrArg k hzη).symm))
  have hzη' : (k ≫ j) (g.fiberι t zη) = f.fiberι (f x) η.1.1 := by
    change j (k _) = _
    rw [hzη, hy, hpη']
  have hgen := mem_genericPoints_fiber_of_injective f g (k ≫ j) i
    (k ≫ j).isClosedEmbedding.injective (fun w => hcond (k w)) t (f x) hbase η zη hzη'
    fun z hz => ⟨φ z, (hz.map hφ).mem_open (e.isOpenMap _ (U.2.preimage continuous_subtype_val))
      ⟨a, ha, hφa⟩, rfl⟩
  have hcomp : closure ({zη} : Set (g.fiber t)) ∈ irreducibleComponents (g.fiber t) := by
    rw [isGenericPoint_def.mp (genericPoints.isGenericPoint ⟨zη, hgen⟩)]
    exact (genericPoints.component ⟨zη, hgen⟩).2
  have hflat : AlgebraicGeometry.IsFlatOverAt f'.toLRSHom.toShHom F' (k (g.fiberι t zη)) := by
    rw [show k (g.fiberι t zη) = a.1 by rw [hzη, hy]]
    exact hU ha
  have hrel : k (g.fiberι t zη) ∈ Stacks.Divisors.relativeAssassin f' F' :=
    mem_relativeAssassin_of_isGenericPoint_fibre_closure f' F' x' hx' (reducedPointClosure x') rfl
      t zη hcomp hflat
  rw [hzη, hy,
    ← AlgebraicGeometry.preimage_relativeAssassin_eq_pullback_of_locallyQuasiFinite f i F] at hrel
  rw [← hpη']
  simpa using hrel

/-- **Stacks Project, Tag 05F1.** Let `f : X ⟶ S` be locally of finite type, let `F` be a
quasi-coherent `𝒪_X`-module of finite type and let `ξ` be a point of `Ass_{X/S}(F)`. There is a
nonempty open `V` of the closure of `ξ` such that for every `s` in the image of `V` the generic
points of the fibre `V_s` lie in `Ass_{X/S}(F)`. -/
@[stacks 05F1]
public theorem exists_open_closure_genericPoints_fibre_mem_relativeAssassin
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (ξ : X) (hξ : ξ ∈ Stacks.Divisors.relativeAssassin f F) :
    ∃ V : Set (closure ({ξ} : Set X)), IsOpen V ∧ V.Nonempty ∧
      ∀ s ∈ f '' (Subtype.val '' V),
        ∀ η : genericPoints ((f.fiberι s) ⁻¹' (Subtype.val '' V) : Set (f.fiber s)),
          f.fiberι s η.1.1 ∈ Stacks.Divisors.relativeAssassin f F := by
  classical
  let D := reducedPointClosure (f ξ)
  let T := D.subscheme
  let i := D.subschemeι
  let f' := pullback.snd f i
  let j := pullback.fst f i
  let F' := (Scheme.Modules.pullback j).obj F
  have : F'.IsQuasicoherent := isQuasicoherent_pullbackObj j F
  have : F'.IsFiniteType := by
    dsimp [F']
    exact AlgebraicGeometry.SheafOfModules.pullback_isFiniteType j.toLRSHom.toShHom F
  have : IsIntegral T := isIntegral_reducedPointClosure (f ξ)
  obtain ⟨t₀, ht₀i, ht₀gen⟩ := exists_isGenericPoint_reducedPointClosure (f ξ)
  have ht₀ : t₀ ∈ genericPoints T := by
    simpa [genericPoints_eq_singleton] using ((genericPoint_spec T).eq ht₀gen).symm
  obtain ⟨x', hxj, hxt⟩ := Scheme.Pullback.exists_preimage_pullback ξ t₀ ht₀i.symm
  have hxpoint : f' x' = t₀ := by simpa [f'] using hxt
  have hxrel : x' ∈ Stacks.Divisors.relativeAssassin f' F' := by
    rw [← AlgebraicGeometry.preimage_relativeAssassin_eq_pullback_of_locallyQuasiFinite f i F]
    change j x' ∈ Stacks.Divisors.relativeAssassin f F
    exact hxj ▸ hξ
  obtain ⟨U, hx'U, hUflat⟩ :=
    exists_open_subset_flatLocus_of_isIntegral_base f' F' x' (by rwa [hxpoint])
  let e := closureHomeomorph j x' ξ hxj
  refine ⟨e '' (Subtype.val ⁻¹' (U : Set (pullback (C := Scheme.{u}) f i))),
    e.isOpenMap _ (U.2.preimage continuous_subtype_val),
    ⟨e ⟨x', subset_closure rfl⟩, ⟨x', subset_closure rfl⟩, hx'U, rfl⟩, ?_⟩
  rintro _ ⟨x, -, rfl⟩ η
  exact fiberι_mem_relativeAssassin_of_subset_flatLocus f i F x' hxrel U hUflat ξ hxj x η

/-- Let `h : Z ⟶ Y` be locally of finite type and quasi-compact, let `η` be the generic point of
`Y` and let `O` be an open of `Z` containing a point over `η`. Then the image of `O` contains a
nonempty open of `Y`. -/
private theorem exists_open_subset_image_of_isGenericPoint {Z Y : Scheme.{u}} (h : Z ⟶ Y)
    [LocallyOfFiniteType h] [QuasiCompact h] (η : Y) (hη : IsGenericPoint η Set.univ)
    (O : Z.Opens) (z₀ : Z) (hz₀O : z₀ ∈ O) (hz₀ : h z₀ = η) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ ∀ y ∈ V, ∃ w ∈ O, h w = y := by
  obtain ⟨V', hV'aff, hηV', -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := η) (U := ⊤) trivial
  have hz₀mem : z₀ ∈ O ⊓ h ⁻¹ᵁ V' := by
    refine ⟨hz₀O, ?_⟩
    change h z₀ ∈ V'
    rwa [hz₀]
  obtain ⟨W, hWaff, hz₀W, hWle⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Z) (x := z₀) hz₀mem
  have hWV' : W ≤ h ⁻¹ᵁ V' := fun w hw => (hWle hw).2
  have : IsAffine W.toScheme := hWaff
  have : IsAffine V'.toScheme := hV'aff
  let g : W.toScheme ⟶ V'.toScheme := h.resLE V' W hWV'
  have : LocallyOfFiniteType g := by dsimp only [g]; infer_instance
  let η' : V'.toScheme := ⟨η, hηV'⟩
  have hη'gen : IsGenericPoint η' Set.univ := by
    rw [isGenericPoint_def, V'.ι.isEmbedding.closure_eq_preimage_closure_image,
      Set.image_singleton, Scheme.Opens.ι_apply, isGenericPoint_def.mp hη]
    simp
  have : IrreducibleSpace V'.toScheme := by
    rw [irreducibleSpace_def]
    exact hη'gen.isIrreducible
  have hgz₀ : g ⟨z₀, hz₀W⟩ = η' :=
    Subtype.ext ((h.coe_resLE_apply hWV' ⟨z₀, hz₀W⟩).trans hz₀)
  obtain ⟨w₀, -⟩ : (⟨z₀, hz₀W⟩ : W.toScheme) ∈ Set.range (g.fiberι η') :=
    (g.range_fiberι η').ge hgz₀
  obtain ⟨V₁, hV₁ne, hV₁surj⟩ :=
    exists_nonempty_open_surjective_baseChange g η' hη'gen ⟨w₀⟩
  refine ⟨V'.ι ''ᵁ V₁, ?_, ?_⟩
  · obtain ⟨y₁, hy₁⟩ := hV₁ne
    exact ⟨y₁.1, (V'.mem_ι_image_iff).mpr hy₁⟩
  · rintro y ⟨y₁, hy₁V₁, hy₁y⟩
    have hs : (⟨y₁, hy₁V₁⟩ : V₁.toScheme) ∈ Set.range (pullback.snd g V₁.ι) :=
      hV₁surj.surj (⟨y₁, hy₁V₁⟩ : V₁.toScheme)
    rw [Scheme.Pullback.range_snd] at hs
    obtain ⟨w, hw⟩ := hs
    have h3 : (g w).1 = y := by rw [hw]; exact hy₁y
    exact ⟨w.1, (hWle w.2).1, (h.coe_resLE_apply hWV' w).symm.trans h3⟩

/-- Let `f` be locally of finite type and quasi-compact, let `η` be the generic point of `Y` and
let `x₀` be a point over `η` lying in an open `O`. Then the image of `O ∩ closure {x₀}` contains a
nonempty open of `Y`. -/
private theorem exists_open_subset_image_inter_closure {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (η : Y) (hη : IsGenericPoint η Set.univ)
    (x₀ : X) (hx₀ : f x₀ = η) (O : X.Opens) (hx₀O : x₀ ∈ O) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧
      ∀ y ∈ V, y ∈ f '' ((O : Set X) ∩ closure ({x₀} : Set X)) := by
  let Z : X.IdealSheafData := reducedPointClosure x₀
  have hZ : Set.range Z.subschemeι = closure ({x₀} : Set X) :=
    range_subschemeι_reducedPointClosure x₀
  obtain ⟨z₀, hz₀⟩ : x₀ ∈ Set.range Z.subschemeι := by
    rw [hZ]
    exact subset_closure rfl
  obtain ⟨V, hV, hVimg⟩ := exists_open_subset_image_of_isGenericPoint (Z.subschemeι ≫ f) η hη
    (Z.subschemeι ⁻¹ᵁ O) z₀ (by change Z.subschemeι z₀ ∈ O; rwa [hz₀])
    (by change f (Z.subschemeι z₀) = η; rwa [hz₀])
  refine ⟨V, hV, fun y hy => ?_⟩
  obtain ⟨w, hwO, rfl⟩ := hVimg y hy
  exact ⟨Z.subschemeι w, ⟨hwO, hZ ▸ ⟨w, rfl⟩⟩, rfl⟩

/-- **Stacks Project, Tag 05KN.** Let `f : X ⟶ Y` be a finite type morphism, `F` a
quasi-coherent `𝒪_X`-module of finite type and `U ⊆ X` open, and let `Y` be irreducible with
generic point `η`. If the associated points of `F` on the fibre over `η` are not all contained
in `U`, then the same failure of containment holds on the fibre over every point of some
nonempty open of `Y`. -/
@[stacks 05KN, ega "IV 1.8.6" "second assertion"]
public theorem exists_open_forall_not_associatedPoints_fibre_subset {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (U : X.Opens)
    [IrreducibleSpace Y] (η : Y) (hη : IsGenericPoint η Set.univ)
    (hηU : ¬ Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback (f.fiberι η)).obj F) ⊆ f.fiberι η ⁻¹' (U : Set X)) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ ∀ y ∈ V,
      ¬ Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback (f.fiberι y)).obj F) ⊆ f.fiberι y ⁻¹' (U : Set X) := by
  classical
  obtain ⟨ξ, hξass, hξU⟩ := Set.not_subset.mp hηU
  have hx₀rel : f.fiberι η ξ ∈ Stacks.Divisors.relativeAssassin f F :=
    (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin f F η ξ).mp hξass
  set x₀ : X := f.fiberι η ξ
  have hclU : ∀ z ∈ closure ({x₀} : Set X), z ∉ (U : Set X) := fun z hz hzU =>
    hξU ((specializes_iff_mem_closure.mpr hz).mem_open U.2 hzU)
  obtain ⟨V₀, hV₀open, hV₀ne, hV₀prop⟩ :=
    exists_open_closure_genericPoints_fibre_mem_relativeAssassin f F x₀ hx₀rel
  obtain ⟨O, hOopen, hOeq⟩ := isOpen_induced_iff.mp hV₀open
  have hV₀eq : Subtype.val '' V₀ = O ∩ closure ({x₀} : Set X) := by
    rw [← hOeq]
    ext z
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff]
    exact ⟨fun ⟨w, hw, hwz⟩ => ⟨hwz ▸ hw, hwz ▸ w.2⟩, fun ⟨hzO, hzc⟩ => ⟨⟨z, hzc⟩, hzO, rfl⟩⟩
  have hx₀O : x₀ ∈ O := by
    obtain ⟨v, hv⟩ := hV₀ne
    rw [← hOeq] at hv
    exact (specializes_iff_mem_closure.mpr v.2).mem_open hOopen hv
  obtain ⟨V, hVne, hVimg⟩ :=
    exists_open_subset_image_inter_closure f η hη x₀ (f.apply_fiberι η ξ) ⟨O, hOopen⟩ hx₀O
  refine ⟨V, hVne, fun y hy => ?_⟩
  have hyimg : y ∈ f '' (Subtype.val '' V₀) := by
    rw [hV₀eq]
    exact hVimg y hy
  obtain ⟨x₁, ⟨hx₁O, hx₁cl⟩, hx₁y⟩ := hVimg y hy
  obtain ⟨b, hb⟩ : x₁ ∈ Set.range (f.fiberι y) :=
    (f.range_fiberι y).ge hx₁y
  have hSeq : ((f.fiberι y) ⁻¹' (Subtype.val '' V₀) : Set (f.fiber y)) =
      ((f.fiberι y) ⁻¹' O) ∩ ((f.fiberι y) ⁻¹' closure ({x₀} : Set X)) := by
    rw [hV₀eq, Set.preimage_inter]
  have : QuasiSober (((f.fiberι y) ⁻¹' O : Set (f.fiber y))) :=
    (hOopen.preimage (f.fiberι y).continuous).isOpenEmbedding_subtypeVal.quasiSober
  have : QuasiSober (((f.fiberι y) ⁻¹' (Subtype.val '' V₀) : Set (f.fiber y))) := by
    rw [hSeq]
    exact QuasiSober.inter_of_isClosed_of_quasiSober_left _
      (isClosed_closure.preimage (f.fiberι y).continuous)
  have hbS : b ∈ ((f.fiberι y) ⁻¹' (Subtype.val '' V₀) : Set (f.fiber y)) := by
    change f.fiberι y b ∈ Subtype.val '' V₀
    rw [hb, hV₀eq]
    exact ⟨hx₁O, hx₁cl⟩
  obtain ⟨c, hc⟩ := genericPoints_nonempty
    (⟨b, hbS⟩ : ((f.fiberι y) ⁻¹' (Subtype.val '' V₀) : Set (f.fiber y)))
  refine Set.not_subset.mpr ⟨c.1,
    (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin f F y c.1).mpr
      (hV₀prop y hyimg ⟨c, hc⟩), fun hcU => hclU _ ?_ hcU⟩
  obtain ⟨v, -, hveq⟩ : f.fiberι y c.1 ∈ Subtype.val '' V₀ := c.2
  exact hveq ▸ v.2

end Stacks.RelativeAssassin

end
