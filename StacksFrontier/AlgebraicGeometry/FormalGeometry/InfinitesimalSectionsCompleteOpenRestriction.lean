module

public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsAtFactor
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerRestriction
public import StacksFrontier.AlgebraicGeometry.LimitSectionsIdentification.Sections
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.IdealSheafComap

/-!
# Infinitesimal section completeness passes to an open neighbourhood

Let `i : Y ⟶ X` be a closed immersion and let `W ⊆ X` be an open containing the image of `i`, so
that `i` factors as `j ≫ W.ι` through a closed immersion `j : Y ⟶ W`. For a quasi-coherent
`𝒪_X`-module `F` this file proves that if `Γ(X, F)` is the inverse limit of the sections of `F` on
the infinitesimal neighbourhoods `Y_n` of `Y` in `X`
(`Stacks.Algebraization.IsInfinitesimalSectionsComplete i F`), and if restriction
`Γ(X, F) ⟶ Γ(W, F)` is bijective, then `Γ(W, F|_W)` is the inverse limit of the sections of
`F|_W` on the infinitesimal neighbourhoods of `Y` in `W`.

Two facts do the work. The infinitesimal neighbourhoods of `Y` in `W` are those of `Y` in `X`:
the ideal of `j` is the inverse image along `W.ι` of the ideal of `i`, so the `n`-th neighbourhoods
are cut out by the same ideal on `W`, and both are closed subschemes of `W` (the neighbourhoods
in `X` lie inside `W`). And sections of `F|_W` on such a neighbourhood are sections of `F` on it,
by the comparison of an iterated pullback with the pullback along the composite. Both facts are
stated for an abstract tower of schemes over a base, the predicate being
`Stacks.Algebraization.InfinitesimalTower.IsGlobalSectionsComplete`, of which
`IsInfinitesimalSectionsComplete` is the instance at the tower of infinitesimal neighbourhoods.

## Main definitions

* `Stacks.Algebraization.InfinitesimalTower.IsGlobalSectionsComplete` — global sections of a
  module are the inverse limit of its sections on the terms of a tower.
* `Stacks.Algebraization.nthInfinitesimalNeighbourhoodOverIsoNbhdOver` — the `n`-th
  infinitesimal neighbourhood of `j` in `W` is the `n`-th infinitesimal neighbourhood of `i` in
  `X`, read over `W`.

## Main results

* `Stacks.Algebraization.InfinitesimalTower.IsGlobalSectionsComplete.of_iso` — the predicate is
  invariant under a levelwise isomorphism of towers.
* `Stacks.Algebraization.isGlobalSectionsComplete_nbhdTower` — the predicate passes from the tower
  over `X` to the tower read over `W`, when restriction of global sections to `W` is bijective.
* `Stacks.Algebraization.isInfinitesimalSectionsComplete_of_isOpenImmersion_factor` — **the
  transfer** to the factorization `j : Y ⟶ W`.

## Implementation notes

As in the neighbourhood files this one builds on, maps on sections that cross the identification
`Γ(f_* ℳ, U) = Γ(ℳ, f ⁻¹ᵁ U)` are chained in term mode with `Eq.trans` and `congrArg`. All
compatibilities between the two towers are free: their structure morphisms are closed immersions,
hence monomorphisms, so two morphisms of schemes over the base into a term of either tower agree.

## References

* [Stacks Project, Tag 0EL2](https://stacks.math.columbia.edu/tag/0EL2)
* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

namespace InfinitesimalTower

variable {Z : Scheme.{u}}

/-- **Global sections of `E` are the inverse limit of its sections on the terms of the tower**:
every compatible family of sections on the terms is the family of restrictions of a unique global
section. -/
public def IsGlobalSectionsComplete (T : InfinitesimalTower Z) (E : Z.Modules) : Prop :=
  ∀ s : ∀ n : ℕ, Γ((Scheme.Modules.pullback (T.obj n).hom).obj E, ⊤),
    (∀ (n m : ℕ) (h : n ≤ m), pullbackSectionsMap E (T.trans n m h) (s m) = s n) →
    ∃! t : Γ(E, ⊤), ∀ n : ℕ, pullbackGlobalSections (T.obj n).hom E t = s n

/-- The transition map on sections along a morphism of schemes over the base carries the
restriction of a global section to the restriction of that global section. -/
public theorem pullbackSectionsMap_pullbackGlobalSections (E : Z.Modules) {A B : Over Z}
    (g : A ⟶ B) (t : Γ(E, ⊤)) :
    pullbackSectionsMap E g (pullbackGlobalSections B.hom E t) =
      pullbackGlobalSections A.hom E t :=
  pullbackSectionsAt_trans E g (Opens.map_top B.hom.base) (Opens.map_top A.hom.base) t

/-- The transition map on sections along an identity is the identity, for a quasi-coherent
module. -/
public theorem pullbackSectionsMap_id_apply (E : Z.Modules) [E.IsQuasicoherent] (A : Over Z)
    (x : Γ((Scheme.Modules.pullback A.hom).obj E, ⊤)) :
    pullbackSectionsMap E (𝟙 A) x = x := by
  rw [Stacks.LimitSectionsIdentification.pullbackSectionsMap_eq_functor, op_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  rfl

/-- The transition map on sections along a composite, applied to a section. -/
public theorem pullbackSectionsMap_comp_apply (E : Z.Modules) [E.IsQuasicoherent]
    {A B C : Over Z} (f : A ⟶ B) (g : B ⟶ C)
    (x : Γ((Scheme.Modules.pullback C.hom).obj E, ⊤)) :
    pullbackSectionsMap E (f ≫ g) x = pullbackSectionsMap E f (pullbackSectionsMap E g x) := by
  rw [Stacks.LimitSectionsIdentification.pullbackSectionsMap_comp]
  rfl

/-- **The predicate is invariant under a levelwise isomorphism of towers** compatible with the
transition maps, for a quasi-coherent module. -/
public theorem IsGlobalSectionsComplete.of_iso {T T' : InfinitesimalTower Z} (E : Z.Modules)
    [E.IsQuasicoherent] (φ : ∀ n : ℕ, T.obj n ≅ T'.obj n)
    (hφ : ∀ (n m : ℕ) (h : n ≤ m), T.trans n m h ≫ (φ m).hom = (φ n).hom ≫ T'.trans n m h)
    (h : T'.IsGlobalSectionsComplete E) : T.IsGlobalSectionsComplete E := by
  have hφ' : ∀ (n m : ℕ) (h : n ≤ m),
      T'.trans n m h ≫ (φ m).inv = (φ n).inv ≫ T.trans n m h := by
    intro n m hnm
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hφ n m hnm, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  intro s hs
  let s' : ∀ n : ℕ, Γ((Scheme.Modules.pullback (T'.obj n).hom).obj E, ⊤) :=
    fun n => pullbackSectionsMap E (φ n).inv (s n)
  have hs' : ∀ (n m : ℕ) (h : n ≤ m),
      pullbackSectionsMap E (T'.trans n m h) (s' m) = s' n := by
    intro n m hnm
    refine ((pullbackSectionsMap_comp_apply E _ _ (s m)).symm.trans ?_)
    rw [hφ' n m hnm, pullbackSectionsMap_comp_apply, hs n m hnm]
  have hback : ∀ n : ℕ, pullbackSectionsMap E (φ n).hom (s' n) = s n := fun n =>
    (pullbackSectionsMap_comp_apply E (φ n).hom (φ n).inv (s n)).symm.trans
      ((congrArg (fun g => pullbackSectionsMap E g (s n)) (φ n).hom_inv_id).trans
        (pullbackSectionsMap_id_apply E _ (s n)))
  obtain ⟨t, ht, huniq⟩ := h s' hs'
  refine ⟨t, fun n => ?_, fun t' ht' => huniq t' fun n => ?_⟩
  · exact (pullbackSectionsMap_pullbackGlobalSections E (φ n).hom t).symm.trans
      ((congrArg (pullbackSectionsMap E (φ n).hom) (ht n)).trans (hback n))
  · exact (pullbackSectionsMap_pullbackGlobalSections E (φ n).inv t').symm.trans
      (congrArg (pullbackSectionsMap E (φ n).inv) (ht' n))

end InfinitesimalTower

/-- **Infinitesimal section completeness is global section completeness of the tower of
infinitesimal neighbourhoods.** -/
public theorem isInfinitesimalSectionsComplete_iff_infTower {Y X : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (F : X.Modules) :
    IsInfinitesimalSectionsComplete i F ↔ (infTower i).IsGlobalSectionsComplete F :=
  Iff.rfl

section OpenNeighbourhood

variable {Y X : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (W : X.Opens)
  (hW : Set.range i.base ⊆ W)

/-- On an open `W`, the bijectivity of restriction `Γ(X, F) ⟶ Γ(W, F)` is the bijectivity of the
pullback of global sections along `W ⟶ X`. -/
public theorem bijective_pullbackGlobalSections_ι_of_bijective_restrict (F : X.Modules)
    (hres : Function.Bijective (F.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op)) :
    Function.Bijective (pullbackGlobalSections W.ι F) := by
  have hWW : W.ι ⁻¹ᵁ W = ⊤ := Scheme.Opens.ι_preimage_self W
  have hU : W.ι ''ᵁ (W.ι ⁻¹ᵁ W) = W := by rw [hWW, Scheme.Opens.ι_image_top]
  have hb := bijective_pullbackSectionsOn_ι W F hWW hU
  have hfac : ∀ t : Γ(F, ⊤), pullbackGlobalSections W.ι F t =
      pullbackSectionsOn W.ι F hWW (F.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t) := by
    intro t
    have h1 := pullbackSectionsOn_restrict W.ι F (Opens.map_top W.ι.base) hWW
      (le_top : W ≤ ⊤) (le_refl (⊤ : W.toScheme.Opens)) t
    refine Eq.trans ?_ h1.symm
    have hid : ((Scheme.Modules.pullback W.ι).obj F).presheaf.map
        (homOfLE (le_refl (⊤ : W.toScheme.Opens))).op = 𝟙 _ := by
      rw [show (homOfLE (le_refl (⊤ : W.toScheme.Opens))).op = 𝟙 (op ⊤) from rfl,
        CategoryTheory.Functor.map_id]
    exact (ConcreteCategory.congr_hom hid _).symm
  have heq : (fun t => pullbackGlobalSections W.ι F t) =
      (pullbackSectionsOn W.ι F hWW) ∘ (F.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) :=
    funext hfac
  show Function.Bijective (fun t => pullbackGlobalSections W.ι F t)
  rw [heq]
  exact hb.comp hres

/-- **Global section completeness passes from the tower of infinitesimal neighbourhoods over `X`
to the same tower read over an open neighbourhood `W`**, for the restriction of `F` to `W`,
provided restriction of global sections to `W` is bijective. -/
public theorem isGlobalSectionsComplete_nbhdTower (F : X.Modules)
    (h : (infTower i).IsGlobalSectionsComplete F)
    (hres : Function.Bijective (F.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op)) :
    (nbhdTower i W hW).IsGlobalSectionsComplete ((Scheme.Modules.pullback W.ι).obj F) := by
  have hpb := bijective_pullbackGlobalSections_ι_of_bijective_restrict W F hres
  let e : ∀ n : ℕ, Γ((Scheme.Modules.pullback ((nbhdTower i W hW).obj n).hom).obj
        ((Scheme.Modules.pullback W.ι).obj F), ⊤) ⟶
      Γ((Scheme.Modules.pullback ((infTower i).obj n).hom).obj F, ⊤) := fun n =>
    (pullbackObjFactorIso F ((nbhdTower i W hW).obj n).hom
      (nbhdTower_obj_hom_ι i W hW n)).hom.app ⊤
  have he : ∀ n : ℕ, Function.Bijective (e n) := fun n => bijective_app_of_isIso _ ⊤
  -- restricting a global section through `W` is restricting it directly
  have hcone : ∀ (n : ℕ) (t : Γ(F, ⊤)),
      e n (pullbackGlobalSections ((nbhdTower i W hW).obj n).hom
          ((Scheme.Modules.pullback W.ι).obj F) (pullbackGlobalSections W.ι F t)) =
        pullbackGlobalSections ((infTower i).obj n).hom F t := fun n t =>
    pullbackSectionsAt_factor F ((nbhdTower i W hW).obj n).hom (nbhdTower_obj_hom_ι i W hW n)
      (Opens.map_top W.ι.base) (Opens.map_top ((infTower i).obj n).hom.base) t
  intro s hs
  have hs' : ∀ (n m : ℕ) (hnm : n ≤ m),
      pullbackSectionsMap F ((infTower i).trans n m hnm) (e m (s m)) = e n (s n) := by
    intro n m hnm
    refine Eq.trans ?_ (congrArg (e n) (hs n m hnm))
    exact ((pullbackSectionsMap_apply_eq F ((infTower i).trans n m hnm) (e m (s m))).trans
        (sectionsAt_factor_transition F W.ι ((nbhdTower i W hW).trans n m hnm).left
          (Over.w ((nbhdTower i W hW).trans n m hnm)) (nbhdTower_obj_hom_ι i W hW n)
          (nbhdTower_obj_hom_ι i W hW m) (Over.w ((infTower i).trans n m hnm)) (s m))).trans
      (congrArg (e n) (pullbackSectionsMap_apply_eq ((Scheme.Modules.pullback W.ι).obj F)
        ((nbhdTower i W hW).trans n m hnm) (s m))).symm
  obtain ⟨t, ht, huniq⟩ := h (fun n => e n (s n)) hs'
  refine ⟨pullbackGlobalSections W.ι F t, fun n => (he n).1 ((hcone n t).trans (ht n)),
    fun u hu => ?_⟩
  obtain ⟨t', rfl⟩ := hpb.2 u
  refine congrArg (pullbackGlobalSections W.ι F) (huniq t' fun n => ?_)
  exact (hcone n t').symm.trans (congrArg (e n) (hu n))

variable (j : Y ⟶ W.toScheme) [IsClosedImmersion j] (hj : j ≫ W.ι = i)

omit [IsClosedImmersion j] in
include hj in
/-- The ideal sheaf of the factorization `j` through `W` is the inverse image of that of `i`. -/
public theorem ker_eq_comap_of_isOpenImmersion_factor : j.ker = i.ker.comap W.ι := by
  have H : IsPullback j (𝟙 Y) W.ι i :=
    IsPullback.of_vert_isIso_mono ⟨by rw [hj, Category.id_comp]⟩
  ext U : 2
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact Scheme.ker_ideal_of_isPullback_of_isOpenImmersion i j (𝟙 Y) W.ι H U

/-- The structure morphism of the `n`-th infinitesimal neighbourhood of `i`, read over `W`, is cut
out by the inverse image of the ideal of the `n`-th infinitesimal neighbourhood. -/
public theorem ker_nbhdOver_hom (n : ℕ) :
    (nbhdOver i W hW n).hom.ker = (i.ker ^ (n + 1)).comap W.ι := by
  have H : IsPullback (nbhdOver i W hW n).hom (𝟙 _) W.ι (nthInfinitesimalNeighbourhoodι i n) :=
    IsPullback.of_vert_isIso_mono
      ⟨(nbhdOver_hom_ι i W hW n).trans (Category.id_comp (nthInfinitesimalNeighbourhoodι i n)).symm⟩
  rw [← ker_nthInfinitesimalNeighbourhoodι i n]
  ext U : 2
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact Scheme.ker_ideal_of_isPullback_of_isOpenImmersion (nthInfinitesimalNeighbourhoodι i n)
    (nbhdOver i W hW n).hom (𝟙 _) W.ι H U

/-- The structure morphism of the `n`-th infinitesimal neighbourhood of `i`, read over `W`, is a
closed immersion. -/
public instance isClosedImmersion_nbhdOver_hom (n : ℕ) :
    IsClosedImmersion (nbhdOver i W hW n).hom := by
  have H : IsPullback (nbhdOver i W hW n).hom (𝟙 _) W.ι (nthInfinitesimalNeighbourhoodι i n) :=
    IsPullback.of_vert_isIso_mono
      ⟨(nbhdOver_hom_ι i W hW n).trans (Category.id_comp (nthInfinitesimalNeighbourhoodι i n)).symm⟩
  exact MorphismProperty.of_isPullback H.flip (isClosedImmersion_nthInfinitesimalNeighbourhoodι i n)

include hj in
/-- The two closed subschemes of `W` — the `n`-th infinitesimal neighbourhood of `j`, and the
`n`-th infinitesimal neighbourhood of `i` read over `W` — have the same ideal sheaf. -/
public theorem ker_nthInfinitesimalNeighbourhoodι_eq_ker_nbhdOver_hom (n : ℕ) :
    (nthInfinitesimalNeighbourhoodι j n).ker = (nbhdOver i W hW n).hom.ker := by
  rw [ker_nthInfinitesimalNeighbourhoodι, ker_nbhdOver_hom,
    Scheme.IdealSheafData.comap_pow_of_isOpenImmersion,
    ker_eq_comap_of_isOpenImmersion_factor i W j hj]

include hj in
/-- **The `n`-th infinitesimal neighbourhood of `j` in `W` is the `n`-th infinitesimal
neighbourhood of `i` in `X`, read over `W`.** Both are closed subschemes of `W` with the same ideal
sheaf. -/
public def nthInfinitesimalNeighbourhoodOverIsoNbhdOver (n : ℕ) :
    nthInfinitesimalNeighbourhoodOver j n ≅ nbhdOver i W hW n where
  hom := Over.homMk (IsClosedImmersion.lift (nbhdOver i W hW n).hom
    (nthInfinitesimalNeighbourhoodι j n)
    (ker_nthInfinitesimalNeighbourhoodι_eq_ker_nbhdOver_hom i W hW j hj n).ge)
    (IsClosedImmersion.lift_fac _ _ _)
  inv := Over.homMk (IsClosedImmersion.lift (nthInfinitesimalNeighbourhoodι j n)
    (nbhdOver i W hW n).hom
    (ker_nthInfinitesimalNeighbourhoodι_eq_ker_nbhdOver_hom i W hW j hj n).le)
    (IsClosedImmersion.lift_fac _ _ _)
  hom_inv_id := Stacks.Flatness.over_hom_ext_of_mono_hom
    (inferInstance : Mono (nthInfinitesimalNeighbourhoodι j n)) _ _
  inv_hom_id := Stacks.Flatness.over_hom_ext_of_mono_hom
    (inferInstance : Mono (nbhdOver i W hW n).hom) _ _

include hW hj in
/-- **Transfer of infinitesimal section completeness to an open neighbourhood.** Let
`i : Y ⟶ X` be a closed immersion factoring as `j ≫ W.ι` through a closed immersion `j` into an
open `W`, and let `F` be a quasi-coherent `𝒪_X`-module. If `Γ(X, F)` is the inverse limit of the
sections of `F` on the infinitesimal neighbourhoods of `i`, and restriction `Γ(X, F) ⟶ Γ(W, F)`
is bijective, then `Γ(W, F|_W)` is the inverse limit of the sections of `F|_W` on the
infinitesimal neighbourhoods of `j`. Here `F|_W` is the pullback of `F` along `W ⟶ X`. -/
public theorem isInfinitesimalSectionsComplete_of_isOpenImmersion_factor (F : X.Modules)
    [F.IsQuasicoherent] (h : IsInfinitesimalSectionsComplete i F)
    (hres : Function.Bijective (F.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op)) :
    IsInfinitesimalSectionsComplete j ((Scheme.Modules.pullback W.ι).obj F) :=
  (isInfinitesimalSectionsComplete_iff_infTower j _).2
    (InfinitesimalTower.IsGlobalSectionsComplete.of_iso (T := infTower j) (T' := nbhdTower i W hW)
      _ (nthInfinitesimalNeighbourhoodOverIsoNbhdOver i W hW j hj)
      (fun _ m _ => Stacks.Flatness.over_hom_ext_of_mono_hom
        (inferInstance : Mono (nbhdOver i W hW m).hom) _ _)
      (isGlobalSectionsComplete_nbhdTower i W hW F
        ((isInfinitesimalSectionsComplete_iff_infTower i F).1 h) hres))

end OpenNeighbourhood

end Stacks.Algebraization

end
