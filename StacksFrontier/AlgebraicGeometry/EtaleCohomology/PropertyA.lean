module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.PurelyInseparableDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.SingletonFibre

/-!
# Property (A) for a morphism of schemes

A morphism `f : X ⟶ Y` has property (A) when every point of every scheme étale over `X` is
reached from one piece of a disjoint-union decomposition of an étale base change of `f`. It is
the hypothesis under which pushforward along the small étale sites reflects injections and
surjections.

A separated locally quasi-finite morphism has property (A): the given point of the étale
scheme is isolated in its fibre, so after an étale base change the part of the source carrying
it splits off as a finite open and closed piece which, being finite étale with a single point
over the distinguished point and a purely inseparable residue extension, becomes isomorphic to
an open subscheme of the étale scheme after shrinking the neighbourhood.

Property (A) for an integral morphism reduces to property (A) for finite morphisms: an étale
algebra over an integral algebra descends to an étale algebra over a module-finite subalgebra,
and property (A) passes from a morphism to any morphism over it.

## Main definitions

* `AlgebraicGeometry.HasPropertyA` is property (A).

## Main results

* `AlgebraicGeometry.hasPropertyA_of_locallyQuasiFinite`: a separated locally quasi-finite
  morphism has property (A).
* `AlgebraicGeometry.hasPropertyA_of_isFinite`: a finite morphism has property (A).
* `AlgebraicGeometry.hasPropertyA_of_isIntegralHom_of_forall_isFinite`: an integral morphism
  has property (A) as soon as every finite morphism does.
* `AlgebraicGeometry.hasPropertyA_of_isIntegralHom`: an integral morphism has property (A).

## Implementation notes

A disjoint-union decomposition is represented by an isomorphism from the binary coproduct of
its two pieces, and the étale morphism in the conclusion is supplied as an explicit witness
rather than as an instance, so that the predicate can be used without typeclass search. The
equation imposed on the morphism out of the first piece says exactly that it is a morphism
over the original source scheme.

The descent of the étale algebra is `Algebra.Etale.exists_subalgebra_fg`; the subalgebra it
produces is of finite type, and integral over the base, hence module-finite, so the resulting
model morphism is finite.

## References

* [Stacks Project, Tag 04DL](https://stacks.math.columbia.edu/tag/04DL)
* [Stacks Project, Tag 04DM](https://stacks.math.columbia.edu/tag/04DM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace AlgebraicGeometry

/-- Property (A) for a morphism of schemes: for every scheme `U` étale over the source and
every point `u` of `U` there is an étale morphism `V ⟶ Y`, a decomposition of `X ×_Y V` into
two open and closed pieces, and a morphism over `X` from the first piece to `U` whose image
contains `u`. -/
def HasPropertyA {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ {U : Scheme.{u}} (p : U ⟶ X) [Etale p] (u : U),
    ∃ (V : Scheme.{u}) (g : V ⟶ Y) (_ : Etale g)
      (W W' : Scheme.{u}) (e : (W ⨿ W') ≅ pullback f g) (h : W ⟶ U),
      h ≫ p = coprod.inl ≫ e.hom ≫ pullback.fst f g ∧
        ∃ w : W, h.base w = u

/-- Specialisation of the étale decomposition of isolated fibre points to the single point `s`,
recording in addition that `s` itself is the distinguished point of one of the finite pieces.
A point of the source of a separated locally quasi-finite morphism is isolated in its fibre, so
there is an étale neighbourhood `V` of its image over which the base change splits into finite
open and closed pieces, one of which meets the distinguished fibre exactly in a point lying
over `s`. -/
private theorem exists_etaleNeighborhood_decomposition_through_point {S T : Scheme.{u}}
    (q : S ⟶ T) (s : S) [IsSeparated q] [LocallyOfFiniteType q] [LocallyQuasiFinite q] :
    ∃ (V : EtaleNeighborhood T (q s))
      (m : Fin 1 → ℕ)
      (D : Option (Σ i, Fin (m i)) → (pullback q V.toBase).Opens)
      (v : ∀ i j, D (some ⟨i, j⟩)),
      Set.PairwiseDisjoint Set.univ (fun k ↦ (D k).1) ∧
      (⋃ k, (D k).1) = Set.univ ∧
      (∀ k, IsClopen (D k).1) ∧
      (∀ i j,
        let V' := D (some ⟨i, j⟩)
        let g := V'.ι ≫ pullback.snd q V.toBase
        IsFinite g ∧
          g ⁻¹' {V.point} = {v i j} ∧
          (V'.ι ≫ pullback.fst q V.toBase) (v i j) = q.fiberι (q s) (q.asFiber s) ∧
          ∃ hvu : g (v i j) = V.point,
            ((V.scheme.residueFieldCongr hvu).inv ≫
              g.residueFieldMap (v i j)).hom.IsPurelyInseparable) ∧
      (∀ w : D none,
        ((D none).ι ≫ pullback.snd q V.toBase) w = V.point →
          ∀ _ : Fin 1, ((D none).ι ≫ pullback.fst q V.toBase) w ≠
            q.fiberι (q s) (q.asFiber s)) ∧
      ∃ j : Fin (m 0),
        ((D (some ⟨0, j⟩)).ι ≫ pullback.fst q V.toBase) (v 0 j) = s := by
  let x : Fin 1 → q.fiber (q s) := fun _ => q.asFiber s
  have hxi : ∀ i, IsIsolatedPoint (x i) := fun i => by
    rw [isIsolatedPoint_iff]
    exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (q.quasiFiniteAt s)
  obtain ⟨V, m, D, v, hdisj, hcover, hclopen, hpieces, hrest⟩ :=
    exists_etaleNeighborhood_purelyInseparable_decomposition
      q 1 (q s) x (fun _ _ _ => Subsingleton.elim _ _) hxi
  refine ⟨V, m, D, v, hdisj, hcover, hclopen, hpieces, hrest, ?_⟩
  obtain ⟨z, hzfst, hzsnd⟩ :=
    Scheme.Pullback.exists_preimage_pullback s V.point V.map_point.symm
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcover.ge (Set.mem_univ z))
  cases k with
  | none =>
    let znone : (D none).toScheme := ⟨z, hk⟩
    have hb' : ((D none).ι ≫ pullback.fst q V.toBase) znone ≠
        q.fiberι (q s) (x 0) := by simpa using hrest znone (by simpa [hzsnd]) 0
    exact (hb' (hzfst.trans (q.fiberι_asFiber s).symm)).elim
  | some a =>
    obtain ⟨i, j⟩ := a
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact ⟨j, (hpieces 0 j).2.2.1.trans (q.fiberι_asFiber s)⟩

/-- In a tower `C ⟶ T ⟶ S` of morphisms of schemes, if the residue field extension of the
composite at a point `z` of `C` is purely inseparable, then so is the residue field extension
of `C ⟶ T` at `z`. -/
theorem isPurelyInseparable_residueFieldMap_of_comp {C T S : Scheme.{u}} (r : C ⟶ T)
    (s : T ⟶ S) (g : C ⟶ S) (hrs : r ≫ s = g) (z : C) {x : S} (hz : g z = x)
    (hpure : ((S.residueFieldCongr hz).inv ≫ g.residueFieldMap z).hom.IsPurelyInseparable) :
    let hxs : r z = r z := rfl
    letI := ((T.residueFieldCongr hxs).inv ≫ r.residueFieldMap z).hom.toAlgebra
    IsPurelyInseparable (T.residueField (r z)) (C.residueField z) := by
  have hrz : s (r z) = g z := congrArg (fun k => k z) hrs
  let K := S.residueField x
  let L := T.residueField (r z)
  let M := C.residueField z
  let α : CommRingCat.of K ⟶ CommRingCat.of M :=
    (S.residueFieldCongr hz).inv ≫ g.residueFieldMap z
  let γ : CommRingCat.of K ⟶ CommRingCat.of L :=
    (S.residueFieldCongr (hrz.trans hz)).inv ≫ s.residueFieldMap (r z)
  let β : CommRingCat.of L ⟶ CommRingCat.of M := r.residueFieldMap z
  have hmaps : s.residueFieldMap (r z) ≫ r.residueFieldMap z =
      (S.residueFieldCongr hrz).hom ≫ g.residueFieldMap z :=
    (Scheme.residueFieldMap_comp r s z).symm.trans (Scheme.Hom.residueFieldMap_congr hrs z)
  have hcomp : γ ≫ β = α := by
    dsimp [γ, β, α]
    simp only [Category.assoc, hmaps]
    rw [← Category.assoc, ← Iso.trans_hom, Scheme.residueFieldCongr_trans]
  let algKL : Algebra K L := γ.hom.toAlgebra
  let algLM : Algebra L M := β.hom.toAlgebra
  let algKM : Algebra K M := α.hom.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' <| by
    ext a
    change α.hom a = β.hom (γ.hom a)
    exact (congrArg (fun φ : K →+* M => φ a) (congrArg CommRingCat.Hom.hom hcomp)).symm
  have : IsPurelyInseparable K M := hpure
  exact IsPurelyInseparable.tower_top K L M

/-- For a universally closed morphism `g : X ⟶ S` and an open `R` of `X` containing the fibre
over `x`, some open neighbourhood of `x` has preimage contained in `R`. -/
theorem exists_opens_forall_mem_of_fiber_subset {X S : Scheme.{u}} (g : X ⟶ S)
    [UniversallyClosed g] (R : X.Opens) (x : S) (hx : ∀ a, g a = x → a ∈ R) :
    ∃ V : S.Opens, x ∈ V ∧ ∀ a, g a ∈ V → a ∈ R := by
  refine ⟨⟨(g.base '' (R : Set X)ᶜ)ᶜ, (g.isClosedMap _ R.2.isClosed_compl).isOpen_compl⟩,
    ?_, fun a ha => ?_⟩
  · change x ∉ g.base '' (R : Set X)ᶜ
    rintro ⟨a, ha, rfl⟩
    exact ha (hx a rfl)
  · by_contra h
    exact (show g a ∉ g.base '' (R : Set X)ᶜ from ha) ⟨a, h, rfl⟩

/-- Two complementary opens of a scheme decompose it as the coproduct of their open
subschemes, the first coprojection being the inclusion of the first open. -/
theorem exists_coprodIso_of_isCompl {T : Scheme.{u}} {W W' : T.Opens} (h : IsCompl W W') :
    ∃ e : W.toScheme ⨿ W'.toScheme ≅ T, coprod.inl ≫ e.hom = W.ι := by
  obtain ⟨H⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl W.ι W'.ι
    (by simpa [Scheme.Opens.opensRange_ι] using h)
  exact ⟨(coprodIsCoprod W.toScheme W'.toScheme).coconePointUniqueUpToIso H,
    IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod W.toScheme W'.toScheme) H
      ⟨WalkingPair.left⟩⟩

/-- A closed open set and its complement are complementary opens. -/
theorem isCompl_opens_compl_of_isClosed {T : Type*} [TopologicalSpace T]
    (W : TopologicalSpace.Opens T) (hW : IsClosed (W : Set T)) :
    IsCompl W ⟨(W : Set T)ᶜ, hW.isOpen_compl⟩ := by
  refine ⟨disjoint_iff.mpr ?_, codisjoint_iff.mpr ?_⟩ <;>
    apply TopologicalSpace.Opens.ext <;> ext x <;> simp

/-- The images of the two pieces of a decomposition `W ⨿ W' ≅ T` are complementary opens. -/
theorem isCompl_opensRange_inl_inr_comp {T W W' : Scheme.{u}} (e : W ⨿ W' ≅ T) :
    IsCompl (coprod.inl ≫ e.hom).opensRange (coprod.inr ≫ e.hom).opensRange := by
  have h := (isCompl_opensRange_inl_inr W W').map e.inv.base.frameHom
  change IsCompl (e.inv ⁻¹ᵁ (coprod.inl : W ⟶ W ⨿ W').opensRange)
    (e.inv ⁻¹ᵁ (coprod.inr : W' ⟶ W ⨿ W').opensRange) at h
  rw [Scheme.Hom.inv_preimage, Scheme.Hom.inv_preimage] at h
  simpa [Scheme.Hom.opensRange_comp] using h

/-- A point of `U` has an affine open neighbourhood mapping into an affine open of `Y`. -/
private theorem exists_isAffineOpen_le_preimage {U Y : Scheme.{u}} (q : U ⟶ Y) (u : U) :
    ∃ (B : Y.Opens) (A : U.Opens), IsAffineOpen B ∧ IsAffineOpen A ∧ u ∈ A ∧ A ≤ q ⁻¹ᵁ B := by
  obtain ⟨_, ⟨B, hB, rfl⟩, hyB, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (a := q u) (by trivial) isOpen_univ
  obtain ⟨_, ⟨A, hA, rfl⟩, huA, hAB⟩ := U.isBasis_affineOpens.exists_subset_of_mem_open
    (show u ∈ q ⁻¹ᵁ B from hyB) (q ⁻¹ᵁ B).2
  exact ⟨B, A, hB, hA, huA, hAB⟩

/-- Property (A) for `f` can be checked on schemes `U` étale over the source for which the
composite `U ⟶ Y` is separated. -/
theorem hasPropertyA_of_forall_isSeparated {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : ∀ {U : Scheme.{u}} (p : U ⟶ X) [Etale p] [IsSeparated (p ≫ f)] (u : U),
      ∃ (V : Scheme.{u}) (g : V ⟶ Y) (_ : Etale g) (W W' : Scheme.{u})
        (e : (W ⨿ W') ≅ pullback f g) (h : W ⟶ U),
        h ≫ p = coprod.inl ≫ e.hom ≫ pullback.fst f g ∧ ∃ w : W, h.base w = u) :
    HasPropertyA f := by
  intro U p _ u
  obtain ⟨B, A, hB, hA, huA, hAB⟩ := exists_isAffineOpen_le_preimage (p ≫ f) u
  have : IsAffine (Scheme.Opens.toScheme A) := hA
  have : IsAffine (Scheme.Opens.toScheme B) := hB
  have : IsSeparated ((Scheme.Opens.ι A ≫ p) ≫ f) := by
    rw [Category.assoc, ← Scheme.Hom.resLE_comp_ι (p ≫ f) hAB, IsSeparated.comp_iff]
    exact IsSeparated.of_isAffineHom _
  obtain ⟨V, g, hg, W, W', e, h, hh, w, hw⟩ := H (Scheme.Opens.ι A ≫ p) ⟨u, huA⟩
  exact ⟨V, g, hg, W, W', e, h ≫ Scheme.Opens.ι A, by rw [Category.assoc, hh], w, by simp [hw]⟩

/-- An open immersion with closed image into an étale base change `V ×_Y X`, together with a map
to `U` over `X` hitting `u`, gives the decomposition required by property (A) at `u`. -/
theorem exists_decomposition_of_isOpenImmersion {X Y U V E : Scheme.{u}} (f : X ⟶ Y)
    (p : U ⟶ X) (g : V ⟶ Y) [Etale g] (k : E ⟶ pullback g f) [IsOpenImmersion k]
    (hk : IsClosed (Set.range k.base)) (a : E ⟶ U)
    (ha : a ≫ p = k ≫ pullback.snd g f) {u : U} (x : E) (hx : a x = u) :
    ∃ (V : Scheme.{u}) (g : V ⟶ Y) (_ : Etale g) (W W' : Scheme.{u})
      (e : (W ⨿ W') ≅ pullback f g) (h : W ⟶ U),
      h ≫ p = coprod.inl ≫ e.hom ≫ pullback.fst f g ∧ ∃ w : W, h.base w = u := by
  obtain ⟨e, he⟩ := exists_coprodIso_of_isCompl (isCompl_opens_compl_of_isClosed k.opensRange hk)
  refine ⟨V, g, inferInstance, _, _, e ≪≫ pullbackSymmetry g f, k.isoOpensRange.inv ≫ a, ?_,
    k.isoOpensRange.hom x, by simp [hx]⟩
  simp only [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst, reassoc_of% he, ha]
  rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]

/-- A finite étale `r : C ⟶ T` over `b : T ⟶ S` whose composite `g` is finite with fibre `{z}`
over `v` and purely inseparable residue extension at `z` is an isomorphism over an open `O` of
`T`, and `O` contains the preimage under `r` of `g ⁻¹ V₀` for an open neighbourhood `V₀` of
`v`. -/
theorem exists_isIso_morphismRestrict_of_fiber_eq_singleton {C T S : Scheme.{u}} (r : C ⟶ T)
    [IsFinite r] [Etale r] (b : T ⟶ S) (g : C ⟶ S) [IsFinite g] (hrs : r ≫ b = g) (z : C)
    {v : S} (hz : g z = v) (hfib : g ⁻¹' {v} = {z})
    (hpure : ((S.residueFieldCongr hz).inv ≫ g.residueFieldMap z).hom.IsPurelyInseparable) :
    ∃ O : T.Opens, IsIso (r ∣_ O) ∧ ∃ V₀ : S.Opens, v ∈ V₀ ∧ ∀ c, g c ∈ V₀ → c ∈ r ⁻¹ᵁ O := by
  have hz' : b (r z) = v := (congrArg (fun k : C ⟶ S => k z) hrs).trans hz
  have hrfiber : r ⁻¹' {r z} = {z} := by
    ext z'
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun hzt => ?_, ?_⟩
    · refine (Set.ext_iff.mp hfib z').mp ?_
      rw [Set.mem_preimage, Set.mem_singleton_iff, ← hrs]
      exact (congrArg b hzt).trans hz'
    · rintro rfl
      rfl
  obtain ⟨O, htO, hO⟩ := exists_open_restrict_isIso_of_finite_etale_fiber_eq_singleton r (r z) z
    hrfiber (isPurelyInseparable_residueFieldMap_of_comp r b g hrs z hz hpure)
  exact ⟨O, hO, exists_opens_forall_mem_of_fiber_subset g (r ⁻¹ᵁ O) v fun a ha => by
    obtain rfl : a = z := (Set.ext_iff.mp hfib a).mp ha
    exact htO⟩

/-- The base change of `f` along `V₀.ι ≫ b` embeds as an open subscheme of the base change along
`b`, over `X` and over `V₀`, with image the preimage of `V₀`. -/
theorem exists_isOpenImmersion_pullback_comp_ι {X Y S : Scheme.{u}} (f : X ⟶ Y) (b : S ⟶ Y)
    (V₀ : S.Opens) :
    ∃ (j : pullback (V₀.ι ≫ b) f ⟶ pullback f b) (_ : IsOpenImmersion j),
      j ≫ pullback.snd f b = pullback.fst (V₀.ι ≫ b) f ≫ V₀.ι ∧
        j ≫ pullback.fst f b = pullback.snd (V₀.ι ≫ b) f ∧
          ∀ t, pullback.snd f b t ∈ V₀ → t ∈ Set.range j.base := by
  let e0 := pullbackRightPullbackFstIso b f V₀.ι
  let s0 := pullbackSymmetry b f
  let j0 : pullback (V₀.ι ≫ b) f ⟶ pullback f b :=
    e0.inv ≫ pullback.snd V₀.ι (pullback.fst b f) ≫ s0.hom
  have : IsOpenImmersion j0 := by
    dsimp [j0]
    infer_instance
  refine ⟨j0, inferInstance, ?_, ?_, fun t ht => ?_⟩
  · dsimp [j0]
    calc
      e0.inv ≫ pullback.snd V₀.ι (pullback.fst b f) ≫ s0.hom ≫ pullback.snd f b =
          e0.inv ≫ pullback.snd V₀.ι (pullback.fst b f) ≫ pullback.fst b f := by
            simp [s0]
      _ = pullback.fst (V₀.ι ≫ b) f ≫ V₀.ι :=
            pullbackRightPullbackFstIso_inv_snd_fst b f V₀.ι
  · dsimp [j0]
    calc
      e0.inv ≫ pullback.snd V₀.ι (pullback.fst b f) ≫ s0.hom ≫ pullback.fst f b =
          e0.inv ≫ pullback.snd V₀.ι (pullback.fst b f) ≫ pullback.snd b f := by
            simp [s0]
      _ = pullback.snd (V₀.ι ≫ b) f :=
            pullbackRightPullbackFstIso_inv_snd_snd b f V₀.ι
  · let y0 : V₀.toScheme := ⟨pullback.snd f b t, ht⟩
    let tP := s0.inv t
    have htP : pullback.fst b f tP = pullback.snd f b t := by
      change (s0.inv ≫ pullback.fst b f) t = _
      rw [pullbackSymmetry_inv_comp_fst]
    have hjoin : V₀.ι y0 = pullback.fst b f tP := by simpa [y0] using htP.symm
    obtain ⟨zP, -, hzPP⟩ := Scheme.Pullback.exists_preimage_pullback y0 tP hjoin
    refine ⟨e0.hom zP, ?_⟩
    change s0.hom (pullback.snd V₀.ι (pullback.fst b f) (e0.inv (e0.hom zP))) = t
    simp [hzPP, tP]

/-- Let `r : C ⟶ X ×_Y S` be finite and an isomorphism over an open `O`, and let `V₀` be an open
of `S` over which `r` lands in `O`. Then the base change of `r` to `V₀ ×_Y X` is a finite open
immersion, and every point of `C` over `V₀` lies in its source. -/
theorem exists_isOpenImmersion_of_isIso_morphismRestrict {X Y S C : Scheme.{u}} (f : X ⟶ Y)
    (b : S ⟶ Y) (r : C ⟶ pullback f b) [IsFinite r] (g : C ⟶ S)
    (hrs : r ≫ pullback.snd f b = g) (O : (pullback f b).Opens) (hO : IsIso (r ∣_ O))
    (V₀ : S.Opens) (hV₀ : ∀ c, g c ∈ V₀ → c ∈ r ⁻¹ᵁ O) :
    ∃ (E : Scheme.{u}) (k : E ⟶ pullback (V₀.ι ≫ b) f) (_ : IsOpenImmersion k)
      (_ : IsFinite k) (a : E ⟶ C),
      k ≫ pullback.snd (V₀.ι ≫ b) f = a ≫ r ≫ pullback.fst f b ∧
        ∀ c, g c ∈ V₀ → ∃ x, a x = c := by
  obtain ⟨j0, _, hjbase, hjfst, hjrange⟩ := exists_isOpenImmersion_pullback_comp_ι f b V₀
  let k := pullback.snd r j0
  let a := pullback.fst r j0
  have hak : k ≫ j0 = a ≫ r := pullback.condition.symm
  have haO : ∀ x, a x ∈ r ⁻¹ᵁ O := by
    intro x
    refine hV₀ (a x) ?_
    have hx' : pullback.snd f b (r (a x)) = V₀.ι (pullback.fst (V₀.ι ≫ b) f (k x)) := by
      calc
        pullback.snd f b (r (a x)) = pullback.snd f b (j0 (k x)) :=
          congrArg (pullback.snd f b)
            (congrArg (fun m : pullback r j0 ⟶ pullback f b => m x) hak).symm
        _ = V₀.ι (pullback.fst (V₀.ι ≫ b) f (k x)) := by
          simpa using congrArg (fun m : pullback (V₀.ι ≫ b) f ⟶ S => m (k x)) hjbase
    rw [show g (a x) = pullback.snd f b (r (a x)) by
      simpa using (congrArg (fun m : C ⟶ S => m (a x)) hrs).symm, hx']
    exact (pullback.fst (V₀.ι ≫ b) f (k x)).property
  have harange : Set.range a ⊆ Set.range (r ⁻¹ᵁ O).ι := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨a x, haO x⟩, rfl⟩
  let aO := IsOpenImmersion.lift (r ⁻¹ᵁ O).ι a harange
  have haOcomp : aO ≫ (r ⁻¹ᵁ O).ι = a := by simp [aO]
  let rO : (r ⁻¹ᵁ O).toScheme ⟶ O.toScheme := r.resLE O (r ⁻¹ᵁ O) le_rfl
  have : IsIso rO := by
    dsimp [rO]
    rwa [Scheme.Hom.resLE_eq_morphismRestrict]
  have hcO : aO ≫ rO ≫ O.ι = a ≫ r := by
    rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, haOcomp]
  have : IsOpenImmersion (k ≫ j0) := by
    rw [hak, ← hcO]
    infer_instance
  refine ⟨_, k, IsOpenImmersion.of_comp k j0, inferInstance, a, by rw [← hjfst, reassoc_of% hak],
    fun c hc => ?_⟩
  obtain ⟨t0, ht0⟩ := hjrange (r c) (by simpa [← hrs] using hc)
  exact (Scheme.Pullback.exists_preimage_pullback c t0 ht0.symm).imp fun _ hx => hx.1

/-- The decomposition required by property (A) at a point of a scheme `U` étale over the source
of a separated locally quasi-finite morphism `f`, when `U ⟶ Y` is separated. -/
theorem exists_decomposition_of_isSeparated {X Y U : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] (p : U ⟶ X) [Etale p]
    [IsSeparated (p ≫ f)] (u : U) :
    ∃ (V : Scheme.{u}) (g : V ⟶ Y) (_ : Etale g) (W W' : Scheme.{u})
      (e : (W ⨿ W') ≅ pullback f g) (h : W ⟶ U),
      h ≫ p = coprod.inl ≫ e.hom ≫ pullback.fst f g ∧ ∃ w : W, h.base w = u := by
  let q : U ⟶ Y := p ≫ f
  have : IsSeparated q := ‹_›
  have : LocallyQuasiFinite p := (locallyQuasiFinite_of_etale p).2
  obtain ⟨V, m, D, v, _, -, _, hpieces, _, ⟨j, hpoint⟩⟩ :=
    exists_etaleNeighborhood_decomposition_through_point q u
  let C : (pullback q V.toBase).Opens := D (some ⟨0, j⟩)
  obtain ⟨hfinC, hfiberC, _, ⟨hbaseC, hpureC⟩⟩ := hpieces 0 j
  have : IsFinite (C.ι ≫ pullback.snd q V.toBase) := hfinC
  let e := pullbackRightPullbackFstIso f V.toBase p
  let r : C.toScheme ⟶ pullback f V.toBase :=
    C.ι ≫ e.inv ≫ pullback.snd p (pullback.fst f V.toBase)
  have hrbase : r ≫ pullback.snd f V.toBase = C.ι ≫ pullback.snd q V.toBase := by
    dsimp [r, e]
    simp [q, pullbackRightPullbackFstIso_inv_snd_snd, Category.assoc]
  have hrfst : r ≫ pullback.fst f V.toBase = C.ι ≫ pullback.fst q V.toBase ≫ p := by
    dsimp [r, e]
    simp [q, pullbackRightPullbackFstIso_inv_snd_fst]
  have : IsFinite (r ≫ pullback.snd f V.toBase) := by rwa [hrbase]
  have : Etale r := by
    dsimp [r]
    infer_instance
  have : IsFinite r := IsFinite.of_comp r (pullback.snd f V.toBase)
  obtain ⟨O, hO, V₀, hV₀, hV₀O⟩ := exists_isIso_morphismRestrict_of_fiber_eq_singleton r
    (pullback.snd f V.toBase) _ hrbase (v 0 j) hbaseC hfiberC hpureC
  obtain ⟨E, k, _, _, a, hk, ha⟩ :=
    exists_isOpenImmersion_of_isIso_morphismRestrict f V.toBase r _ hrbase O hO V₀ hV₀O
  obtain ⟨x, hx⟩ := ha (v 0 j) ((congrArg (· ∈ V₀) hbaseC).mpr hV₀)
  refine exists_decomposition_of_isOpenImmersion f p (V₀.ι ≫ V.toBase) k ?_
    (a ≫ C.ι ≫ pullback.fst q V.toBase) (by simp only [hk, hrfst, Category.assoc]) x ?_
  · exact k.isClosedMap.isClosed_range
  · change (C.ι ≫ pullback.fst q V.toBase) (a x) = u
    rw [hx]
    exact hpoint

/-- **Stacks Project, Tag 04DL.** A separated locally quasi-finite morphism of schemes has
property (A). -/
@[stacks 04DL]
theorem hasPropertyA_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] : HasPropertyA f :=
  hasPropertyA_of_forall_isSeparated f fun p _ _ u ↦ exists_decomposition_of_isSeparated f p u

/-- A finite morphism of schemes has property (A): it is separated and locally quasi-finite,
so `AlgebraicGeometry.hasPropertyA_of_locallyQuasiFinite` applies. -/
theorem hasPropertyA_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] :
    HasPropertyA f :=
  hasPropertyA_of_locallyQuasiFinite f

/-- An étale algebra over an algebra which is integral over the base descends to an étale
algebra over a module-finite subalgebra. -/
private theorem exists_finite_etale_model {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra.IsIntegral R A]
    [Algebra.Etale A B] :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type v) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      Module.Finite R A₀ ∧ Algebra.Etale A₀ B₀ ∧
        Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀) := by
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, hB⟩ := Algebra.Etale.exists_subalgebra_fg R A B
  exact ⟨A₀, B₀, inferInstance, inferInstance,
    Algebra.finite_iff_isIntegral_and_finiteType.mpr
      ⟨A₀.isIntegral_iff.mpr fun x _ => Algebra.IsIntegral.isIntegral (R := R) x,
        A₀.fg_iff_finiteType.mp hA₀⟩, hB₀, hB⟩

/-- Let `i₀ : W₀ ⟶ T₀` be an open immersion and `h₀ : W₀ ⟶ U₀` a morphism with
`h₀ ≫ p₀ = i₀ ≫ c`. Over the preimage `A` of the range of `i₀` in `X ×_{X₀} T₀` there is a
morphism `A ⟶ U₀ ×_{X₀} X` over `X` whose image contains every point lying over the image of
`h₀`. -/
theorem exists_lift_preimage_opensRange {X X₀ T₀ U₀ W₀ : Scheme.{u}} (π : X ⟶ X₀)
    (c : T₀ ⟶ X₀) (p₀ : U₀ ⟶ X₀) (h₀ : W₀ ⟶ U₀) (i₀ : W₀ ⟶ T₀) [IsOpenImmersion i₀]
    (h : h₀ ≫ p₀ = i₀ ≫ c) :
    ∃ l : (pullback.snd π c ⁻¹ᵁ i₀.opensRange).toScheme ⟶ pullback p₀ π,
      l ≫ pullback.snd p₀ π = (pullback.snd π c ⁻¹ᵁ i₀.opensRange).ι ≫ pullback.fst π c ∧
        ∀ v, pullback.fst p₀ π v ∈ Set.range h₀.base → v ∈ Set.range l.base := by
  let A := pullback.snd π c ⁻¹ᵁ i₀.opensRange
  let a₀ : A.toScheme ⟶ W₀ :=
    (pullback.snd π c).resLE i₀.opensRange A le_rfl ≫ i₀.isoOpensRange.inv
  have ha₀ : a₀ ≫ i₀ = A.ι ≫ pullback.snd π c := by
    dsimp only [a₀]
    rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, Scheme.Hom.resLE_comp_ι]
  have hl : (a₀ ≫ h₀) ≫ p₀ = (A.ι ≫ pullback.fst π c) ≫ π := by
    rw [Category.assoc, h, reassoc_of% ha₀, Category.assoc, pullback.condition]
  refine ⟨pullback.lift (a₀ ≫ h₀) (A.ι ≫ pullback.fst π c) hl, pullback.lift_snd _ _ _, ?_⟩
  rintro v ⟨w₀, hw₀⟩
  let S := pullback (h₀ ≫ p₀) π
  let m : S ⟶ pullback p₀ π :=
    pullback.map (h₀ ≫ p₀) π p₀ π h₀ (𝟙 X) (𝟙 X₀) (by simp) (by simp)
  obtain ⟨z, hz⟩ : v ∈ Set.range m.base := by
    change v ∈ Set.range (pullback.map (h₀ ≫ p₀) π p₀ π h₀ (𝟙 X) (𝟙 X₀) (by simp) (by simp))
    rw [Scheme.Pullback.range_map (h₀ ≫ p₀) π p₀ π h₀ (𝟙 X) (𝟙 X₀) (by simp) (by simp)]
    exact ⟨⟨w₀, hw₀⟩, ⟨pullback.snd p₀ π v, rfl⟩⟩
  obtain ⟨α, hα₁, hα₂⟩ : ∃ α : S ⟶ pullback π c,
      α ≫ pullback.fst π c = pullback.snd (h₀ ≫ p₀) π ∧
        α ≫ pullback.snd π c = pullback.fst (h₀ ≫ p₀) π ≫ i₀ :=
    ⟨pullback.lift (pullback.snd (h₀ ≫ p₀) π) (pullback.fst (h₀ ≫ p₀) π ≫ i₀)
      (by rw [Category.assoc, ← h]; exact pullback.condition.symm),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hrange : Set.range α.base ⊆ Set.range A.ι.base := by
    rintro _ ⟨s, rfl⟩
    refine ⟨⟨α s, ?_⟩, rfl⟩
    change (α ≫ pullback.snd π c) s ∈ i₀.opensRange
    rw [hα₂]
    exact Scheme.Hom.mem_opensRange.mpr ⟨_, rfl⟩
  obtain ⟨αA, hαA⟩ : ∃ αA : S ⟶ A.toScheme, αA ≫ A.ι = α :=
    ⟨IsOpenImmersion.lift A.ι α hrange, IsOpenImmersion.lift_fac _ _ _⟩
  have hfirst : αA ≫ a₀ = pullback.fst (h₀ ≫ p₀) π := by
    rw [← cancel_mono i₀, Category.assoc, ha₀, reassoc_of% hαA, hα₂]
  have hmap : αA ≫ pullback.lift (a₀ ≫ h₀) (A.ι ≫ pullback.fst π c) hl = m := by
    apply pullback.hom_ext
    · dsimp only [m, pullback.map]
      rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, reassoc_of% hfirst]
    · dsimp only [m, pullback.map]
      rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, reassoc_of% hαA, hα₁,
        Category.comp_id]
  refine ⟨αA z, ?_⟩
  simpa using (congrArg (fun k : S ⟶ pullback p₀ π => k z) hmap).trans hz

/-- Property (A) passes from a morphism to any morphism over it: an étale scheme over the
source of the latter which is a base change of an étale scheme over the source of the former
inherits the required decomposition. -/
private theorem hasPropertyA_baseChange
    {X₀ Y X U₀ U : Scheme.{u}} (f₀ : X₀ ⟶ Y) (π : X ⟶ X₀)
    (p₀ : U₀ ⟶ X₀) [Etale p₀] (p : U ⟶ X) [Etale p]
    (eU : U ≅ pullback p₀ π)
    (heU : eU.hom ≫ pullback.snd p₀ π = p)
    (hA : HasPropertyA f₀) (u : U) :
    ∃ (V : Scheme.{u}) (g : V ⟶ Y) (_ : Etale g)
      (W W' : Scheme.{u}) (e : (W ⨿ W') ≅ pullback (π ≫ f₀) g)
      (h : W ⟶ U),
      h ≫ p = coprod.inl ≫ e.hom ≫ pullback.fst (π ≫ f₀) g ∧
        ∃ w : W, h.base w = u := by
  let v : ↑(pullback p₀ π) := eU.hom.base u
  obtain ⟨V, g, hg, W₀, W₀', e₀, h₀, heq₀, ⟨w₀, hw₀⟩⟩ := hA p₀ (pullback.fst p₀ π v)
  obtain ⟨l, hl, hlv⟩ := exists_lift_preimage_opensRange π (pullback.fst f₀ g) p₀ h₀
    (coprod.inl ≫ e₀.hom) (heq₀.trans (Category.assoc _ _ _).symm)
  have hcompl := (isCompl_opensRange_inl_inr_comp e₀).map
    (pullback.snd π (pullback.fst f₀ g)).base.frameHom
  change IsCompl (pullback.snd π (pullback.fst f₀ g) ⁻¹ᵁ (coprod.inl ≫ e₀.hom).opensRange)
    (pullback.snd π (pullback.fst f₀ g) ⁻¹ᵁ (coprod.inr ≫ e₀.hom).opensRange) at hcompl
  obtain ⟨e, heinl⟩ := exists_coprodIso_of_isCompl hcompl
  have heUinv : eU.inv ≫ p = pullback.snd p₀ π := eU.inv_comp_eq.mpr heU.symm
  refine ⟨V, g, hg, _, _, e ≪≫ pullbackRightPullbackFstIso f₀ g π, l ≫ eU.inv, ?_, ?_⟩
  · simp only [Category.assoc, heUinv, hl, Iso.trans_hom, reassoc_of% heinl,
      pullbackRightPullbackFstIso_hom_fst]
  · obtain ⟨w, hw⟩ := hlv v ⟨w₀, hw₀⟩
    exact ⟨w, by simp [hw, v]⟩

/-- Transporting a pullback along an isomorphism of arrows. -/
private noncomputable def pullbackIsoOfIsoArrow
    {X Y X₀ Y₀ V : Scheme.{u}} (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀)
    (eX : X ≅ X₀) (eY : Y ≅ Y₀) (g : V ⟶ Y₀)
    (h : eX.hom ≫ f₀ = f ≫ eY.hom) :
    pullback f₀ g ≅ pullback f (g ≫ eY.inv) := by
  have h' : f₀ ≫ eY.inv = eX.inv ≫ f := by
    rw [Iso.comp_inv_eq, Category.assoc, ← h, Iso.inv_hom_id_assoc]
  let m : pullback f₀ g ⟶ pullback f (g ≫ eY.inv) :=
    pullback.map f₀ g f (g ≫ eY.inv) eX.inv (𝟙 V) eY.inv h' (by simp)
  have : IsIso m := by
    dsimp [m]
    infer_instance
  exact asIso m

/-- Base change of `f` along a morphism into an open `B` of the target is the base change of the
restriction `f ∣_ B`, compatibly with the projections to the source. -/
theorem exists_pullbackIso_morphismRestrict {X Y V : Scheme.{u}} (f : X ⟶ Y) (B : Y.Opens)
    (gLoc : V ⟶ B.toScheme) :
    ∃ e : pullback (f ∣_ B) gLoc ≅ pullback f (gLoc ≫ B.ι),
      e.hom ≫ pullback.fst f (gLoc ≫ B.ι) = pullback.fst (f ∣_ B) gLoc ≫ (f ⁻¹ᵁ B).ι := by
  let eA := pullbackRestrictIsoRestrict f B
  let mOpen : pullback (pullback.snd f B.ι) gLoc ⟶ pullback (f ∣_ B) gLoc :=
    pullback.map (pullback.snd f B.ι) gLoc (f ∣_ B) gLoc eA.hom (𝟙 V) (𝟙 B.toScheme)
      (by rw [Category.comp_id, ← pullbackRestrictIsoRestrict_hom_morphismRestrict])
      (Category.comp_id gLoc)
  have : IsIso mOpen := by
    dsimp [mOpen]
    exact pullback.map_isIso (pullback.snd f B.ι) gLoc (f ∣_ B) gLoc eA.hom (𝟙 V)
      (𝟙 B.toScheme)
      (by rw [Category.comp_id, ← pullbackRestrictIsoRestrict_hom_morphismRestrict])
      (Category.comp_id gLoc)
  refine ⟨(asIso mOpen).symm ≪≫ pullbackLeftPullbackSndIso f B.ι gLoc, ?_⟩
  have hmOpen : mOpen ≫ pullback.fst (f ∣_ B) gLoc =
      pullback.fst (pullback.snd f B.ι) gLoc ≫ eA.hom := by
    dsimp [mOpen, pullback.map]
    rw [pullback.lift_fst]
  have hmOpenInv : (asIso mOpen).inv ≫ pullback.fst (pullback.snd f B.ι) gLoc =
      pullback.fst (f ∣_ B) gLoc ≫ eA.inv := by
    rw [Iso.inv_comp_eq, asIso_hom, reassoc_of% hmOpen, Iso.hom_inv_id, Category.comp_id]
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
    reassoc_of% hmOpenInv]
  exact congrArg (pullback.fst (f ∣_ B) gLoc ≫ ·) (pullbackRestrictIsoRestrict_inv_fst f B)

/-- On affine opens, `resLE` corresponds under `isoSpec` to `Spec` of `appLE`. -/
theorem Scheme.Hom.resLE_comp_isoSpec_hom {U X : Scheme.{u}} (p : U ⟶ X) {A : X.Opens}
    {D : U.Opens} (hA : IsAffineOpen A) (hD : IsAffineOpen D) (hDU : D ≤ p ⁻¹ᵁ A) :
    p.resLE A D hDU ≫ hA.isoSpec.hom = hD.isoSpec.hom ≫ Spec.map (p.appLE A D hDU) := by
  have hcancel : Spec.map (p.appLE A D hDU) ≫ hA.isoSpec.inv =
      hD.isoSpec.inv ≫ p.resLE A D hDU := by
    apply (cancel_mono A.ι).mp
    calc
      Spec.map (p.appLE A D hDU) ≫ hA.isoSpec.inv ≫ A.ι =
          Spec.map (p.appLE A D hDU) ≫ hA.fromSpec := by
        simp
      _ = hD.fromSpec ≫ p := IsAffineOpen.SpecMap_appLE_fromSpec p hA hD hDU
      _ = hD.isoSpec.inv ≫ D.ι ≫ p := by
        simp
      _ = hD.isoSpec.inv ≫ p.resLE A D hDU ≫ A.ι := by
        rw [Scheme.Hom.resLE_comp_ι]
  simpa using (congrArg (fun k : Spec Γ(U, D) ⟶ A.toScheme =>
    hD.isoSpec.hom ≫ k ≫ hA.isoSpec.hom) hcancel).symm

/-- An étale scheme over the spectrum of an integral algebra is the base change of an étale
scheme over a scheme finite over the base. -/
theorem exists_isFinite_etale_model_Spec {R A C : CommRingCat.{u}} (φ : R ⟶ A) (ψ : A ⟶ C)
    (hφ : φ.hom.IsIntegral) (hψ : ψ.hom.Etale) :
    ∃ (X₀ U₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec R) (π : Spec A ⟶ X₀) (p₀ : U₀ ⟶ X₀)
      (_ : IsFinite f₀) (_ : Etale p₀) (eU : Spec C ≅ pullback p₀ π),
      π ≫ f₀ = Spec.map φ ∧ eU.hom ≫ pullback.snd p₀ π = Spec.map ψ := by
  algebraize [φ.hom, ψ.hom]
  have : Algebra.IsIntegral R A := by
    apply algebraMap_isIntegral_iff.mp
    simpa [RingHom.algebraMap_toAlgebra] using hφ
  have : Algebra.Etale A C := by
    apply RingHom.etale_algebraMap.mp
    simpa [RingHom.algebraMap_toAlgebra] using hψ
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, ⟨eAB⟩⟩ := exists_finite_etale_model (R := R) (A := A) (B := C)
  let eRing : CommRingCat.of C ≅ CommRingCat.of (A ⊗[A₀] B₀) :=
    eAB.toRingEquiv.toCommRingCatIso
  let π : Spec A ⟶ Spec (CommRingCat.of A₀) := Spec.map (CommRingCat.ofHom (algebraMap A₀ A))
  let p₀ := Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))
  have hinc : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A₀)
      (A := A) (B := B₀)) ≫ eRing.op.inv.unop = ψ := by
    ext a
    change eAB.symm (Algebra.TensorProduct.includeLeftRingHom a) = ψ.hom a
    simpa [Algebra.TensorProduct.includeLeftRingHom_apply, RingHom.algebraMap_toAlgebra]
      using eAB.symm.commutes a
  refine ⟨_, _, Spec.map (CommRingCat.ofHom (algebraMap R A₀)), π, p₀,
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.mpr hA₀),
    HasRingHomProperty.Spec_iff.mpr <| RingHom.etale_algebraMap.mpr hB₀,
    Scheme.Spec.mapIso eRing.symm.op ≪≫ (pullbackSpecIso A₀ A B₀).symm ≪≫
      pullbackSymmetry π p₀, ?_, ?_⟩
  · dsimp only [π]
    rw [← Spec.map_comp]
    congr 1
  · dsimp
    simp only [Category.assoc, pullbackSymmetry_hom_comp_snd]
    rw [pullbackSpecIso_inv_fst, ← Spec.map_comp, hinc]

/-- Property (A) data at a point of an affine open `D` of `U`, for a model `f₁` of the
restriction `f ∣_ B` along isomorphisms, gives property (A) data for `f` at that point. -/
theorem exists_decomposition_of_affine_model {X Y U X₁ Y₁ : Scheme.{u}} (f : X ⟶ Y)
    (p : U ⟶ X) (B : Y.Opens) (D : U.Opens) (hDU : D ≤ p ⁻¹ᵁ (f ⁻¹ᵁ B)) (f₁ : X₁ ⟶ Y₁)
    (eX : (f ⁻¹ᵁ B).toScheme ≅ X₁) (eY : B.toScheme ≅ Y₁)
    (hmodel : eX.hom ≫ f₁ = (f ∣_ B) ≫ eY.hom) (p₁ : D.toScheme ⟶ X₁)
    (hp₁ : p.resLE (f ⁻¹ᵁ B) D hDU ≫ eX.hom = p₁) (u : U) (hu : u ∈ D)
    (H : ∃ (V : Scheme.{u}) (g : V ⟶ Y₁) (_ : Etale g) (W W' : Scheme.{u})
      (e : (W ⨿ W') ≅ pullback f₁ g) (h : W ⟶ D.toScheme),
      h ≫ p₁ = coprod.inl ≫ e.hom ≫ pullback.fst f₁ g ∧ ∃ w : W, h.base w = ⟨u, hu⟩) :
    ∃ (V : Scheme.{u}) (g : V ⟶ Y) (_ : Etale g) (W W' : Scheme.{u})
      (e : (W ⨿ W') ≅ pullback f g) (h : W ⟶ U),
      h ≫ p = coprod.inl ≫ e.hom ≫ pullback.fst f g ∧ ∃ w : W, h.base w = u := by
  obtain ⟨V, g, hg, W, W', e, h, hh, w, hw⟩ := H
  let gLoc : V ⟶ B.toScheme := g ≫ eY.inv
  obtain ⟨eOpen, hOpen⟩ := exists_pullbackIso_morphismRestrict f B gLoc
  let eModel := pullbackIsoOfIsoArrow (f ∣_ B) f₁ eX eY g hmodel
  have hModel : eModel.hom ≫ pullback.fst (f ∣_ B) gLoc = pullback.fst f₁ g ≫ eX.inv := by
    dsimp [eModel, pullbackIsoOfIsoArrow]
    rw [pullback.lift_fst]
  refine ⟨V, gLoc ≫ B.ι, inferInstance, W, W', e ≪≫ eModel ≪≫ eOpen, h ≫ D.ι, ?_, w, ?_⟩
  · rw [Category.assoc, ← Scheme.Hom.resLE_comp_ι p hDU, (Iso.eq_comp_inv eX).mpr hp₁]
    simp only [Iso.trans_hom, Category.assoc, hOpen, reassoc_of% hModel, reassoc_of% hh]
  · simp [hw]

/-- **Stacks Project, Tag 04DM.** An integral morphism of schemes has property (A), given that
every finite morphism of schemes has it: an étale scheme over the source descends to an étale
scheme over a finite model of the morphism, and property (A) passes to a morphism over that
model. -/
theorem hasPropertyA_of_isIntegralHom_of_forall_isFinite
    (hfin : ∀ {X' Y' : Scheme.{u}} (f' : X' ⟶ Y'), IsFinite f' → HasPropertyA f')
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] : HasPropertyA f := by
  intro U p hp u
  obtain ⟨B, D, hB, hD, huD, hDU⟩ := exists_isAffineOpen_le_preimage (p ≫ f) u
  have hA : IsAffineOpen (f ⁻¹ᵁ B) := IsAffineHom.isAffine_preimage (f := f) B hB
  obtain ⟨X₀, U₀, f₀, π, p₀, hf₀, _, eU, hπf, heU⟩ :=
    exists_isFinite_etale_model_Spec (f.appLE B (f ⁻¹ᵁ B) le_rfl) (p.appLE (f ⁻¹ᵁ B) D hDU)
      (by simpa [Scheme.Hom.appLE_eq_app] using f.isIntegral_app B hB)
      (hp.etale_appLE hA hD hDU)
  have : Etale (Spec.map (p.appLE (f ⁻¹ᵁ B) D hDU)) :=
    HasRingHomProperty.Spec_iff.mpr (hp.etale_appLE hA hD hDU)
  refine exists_decomposition_of_affine_model f p B D hDU (π ≫ f₀) hA.isoSpec hB.isoSpec ?_
    (hD.isoSpec.hom ≫ Spec.map (p.appLE (f ⁻¹ᵁ B) D hDU))
    (Scheme.Hom.resLE_comp_isoSpec_hom p hA hD hDU) u huD
    (hasPropertyA_baseChange f₀ π p₀ (hD.isoSpec.hom ≫ Spec.map (p.appLE (f ⁻¹ᵁ B) D hDU))
      (hD.isoSpec ≪≫ eU) (by simp [heU]) (hfin f₀ hf₀) ⟨u, huD⟩)
  rw [hπf, ← Scheme.Hom.resLE_eq_morphismRestrict]
  exact (Scheme.Hom.resLE_comp_isoSpec_hom f hB hA le_rfl).symm

/-- **Stacks Project, Tag 04DM.** Every integral morphism of schemes has property (A). -/
@[stacks 04DM]
theorem hasPropertyA_of_isIntegralHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] :
    HasPropertyA f :=
  hasPropertyA_of_isIntegralHom_of_forall_isFinite
    (fun f' _ => hasPropertyA_of_isFinite f') f

end AlgebraicGeometry

end
