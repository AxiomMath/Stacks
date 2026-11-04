module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic

/-!
# Closure properties of infinitesimal section completeness

For an immersion `i : Z ⟶ X` of schemes, a module `F` on `X` is *infinitesimally section
complete* when `Γ(X, F) → lim Γ(Z_n, F|_{Z_n})` is bijective, where `Z_n` are the infinitesimal
neighbourhoods of `i`; this is `Stacks.Algebraization.IsInfinitesimalSectionsComplete`, phrased by
the universal property of the inverse limit. This file proves that the condition passes to
retracts, holds for the zero module, is stable under finite biproducts, and is left exact.

## Main results

* `Stacks.Algebraization.isInfinitesimalSectionsComplete_of_retract` — section completeness passes
  to a retract.
* `Stacks.Algebraization.isInfinitesimalSectionsComplete_zero` and
  `Stacks.Algebraization.isInfinitesimalSectionsComplete_biprod` — the zero module is complete, and
  completeness is stable under binary biproducts.
* `Stacks.Algebraization.isInfinitesimalSectionsComplete_bicone_pt` and
  `Stacks.Algebraization.isInfinitesimalSectionsComplete_biproduct` — completeness is stable under
  finite biproducts, stated both for the apex of an arbitrary bilimit bicone and for
  `CategoryTheory.Limits.biproduct`.
* `Stacks.Algebraization.isInfinitesimalSectionsComplete_of_sectionsKernel` — **left exactness**: a
  module whose global sections are the kernel of a map between complete modules, compatibly on the
  infinitesimal neighbourhoods, is complete.

## References

* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject

universe u

namespace Stacks.Algebraization

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- Finite biproducts in the category of modules on a scheme. -/
public instance (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

section Additivity

private lemma app_add_apply {W : Scheme.{u}} {A B : W.Modules} (φ ψ : A ⟶ B) (U : W.Opens)
    (x : Γ(A, U)) : (φ + ψ).app U x = φ.app U x + ψ.app U x := by
  rw [Scheme.Modules.Hom.add_app]
  exact AddCommGrpCat.hom_add_apply (φ.app U) (ψ.app U) x

/-- Evaluating a morphism of modules at a fixed section, as an additive map in the morphism. -/
private def appHom {W : Scheme.{u}} {A B : W.Modules} (U : W.Opens) (x : Γ(A, U)) :
    (A ⟶ B) →+ Γ(B, U) :=
  AddMonoidHom.mk' (fun φ => φ.app U x) (fun φ ψ => app_add_apply φ ψ U x)

private lemma app_sum {W : Scheme.{u}} {A B : W.Modules} (U : W.Opens) {κ : Type*}
    (s : Finset κ) (φ : κ → (A ⟶ B)) (x : Γ(A, U)) :
    (∑ j ∈ s, φ j).app U x = ∑ j ∈ s, (φ j).app U x :=
  map_sum (appHom (B := B) U x) φ s

/-- Pulling a morphism back and evaluating it at a fixed section, as an additive map in the
morphism. -/
private def pullbackApply {W : Scheme.{u}} (g : W ⟶ X) {F G : X.Modules}
    (x : Γ((Scheme.Modules.pullback g).obj F, ⊤)) :
    (F ⟶ G) →+ Γ((Scheme.Modules.pullback g).obj G, ⊤) :=
  AddMonoidHom.mk' (fun φ => ((Scheme.Modules.pullback g).map φ).app ⊤ x)
    (fun φ ψ =>
      (congrArg (fun χ => Scheme.Modules.Hom.app χ ⊤ x)
          ((Scheme.Modules.pullback g).map_add (f := φ) (g := ψ))).trans
        (app_add_apply _ _ ⊤ x))

private lemma appMap_eq_of_eq {W : Scheme.{u}} (g : W ⟶ X) {F G : X.Modules} (φ φ' : F ⟶ G)
    (hφ : φ = φ') (x : Γ((Scheme.Modules.pullback g).obj F, ⊤)) :
    ((Scheme.Modules.pullback g).map φ).app ⊤ x =
      ((Scheme.Modules.pullback g).map φ').app ⊤ x :=
  congrArg (fun χ => Scheme.Modules.Hom.app ((Scheme.Modules.pullback g).map χ) ⊤ x) hφ

private lemma appMap_comp {W : Scheme.{u}} (g : W ⟶ X) {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H)
    (x : Γ((Scheme.Modules.pullback g).obj F, ⊤)) :
    ((Scheme.Modules.pullback g).map ψ).app ⊤ (((Scheme.Modules.pullback g).map φ).app ⊤ x) =
      ((Scheme.Modules.pullback g).map (φ ≫ ψ)).app ⊤ x :=
  (congrArg (fun χ => Scheme.Modules.Hom.app χ ⊤ x)
    ((Scheme.Modules.pullback g).map_comp φ ψ)).symm

private lemma appMap_id {W : Scheme.{u}} (g : W ⟶ X) {F : X.Modules}
    (x : Γ((Scheme.Modules.pullback g).obj F, ⊤)) :
    ((Scheme.Modules.pullback g).map (𝟙 F)).app ⊤ x = x :=
  congrArg (fun χ => Scheme.Modules.Hom.app χ ⊤ x) ((Scheme.Modules.pullback g).map_id F)

private lemma appMap_zero {W : Scheme.{u}} (g : W ⟶ X) {F G : X.Modules}
    (x : Γ((Scheme.Modules.pullback g).obj F, ⊤)) :
    ((Scheme.Modules.pullback g).map (0 : F ⟶ G)).app ⊤ x = 0 :=
  map_zero (pullbackApply (G := G) g x)

private lemma appMap_sum {W : Scheme.{u}} (g : W ⟶ X) {F G : X.Modules} {κ : Type*}
    (s : Finset κ) (φ : κ → (F ⟶ G)) (x : Γ((Scheme.Modules.pullback g).obj F, ⊤)) :
    ((Scheme.Modules.pullback g).map (∑ j ∈ s, φ j)).app ⊤ x =
      ∑ j ∈ s, ((Scheme.Modules.pullback g).map (φ j)).app ⊤ x :=
  map_sum (pullbackApply (G := G) g x) φ s

end Additivity

/-- The image of a compatible family of sections under a morphism of modules is again
compatible. -/
private lemma pullbackMap_app_compatible {F G : X.Modules} (φ : F ⟶ G)
    (x : ∀ n : ℕ, Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj F, ⊤))
    (hx : ∀ (n m : ℕ) (h : n ≤ m),
      pullbackSectionsMap F (nthInfinitesimalNeighbourhoodTransition i h) (x m) = x n)
    (n m : ℕ) (h : n ≤ m) :
    pullbackSectionsMap G (nthInfinitesimalNeighbourhoodTransition i h)
        (((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i m)).map φ).app ⊤ (x m)) =
      ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).map φ).app ⊤ (x n) :=
  (pullbackSectionsMap_natural φ (nthInfinitesimalNeighbourhoodTransition i h) (x m)).trans
    (congrArg (fun z => ((Scheme.Modules.pullback
      (nthInfinitesimalNeighbourhoodι i n)).map φ).app ⊤ z) (hx n m h))

/-- A morphism of modules carries sections with prescribed pullbacks to sections with the
correspondingly pushed-forward pullbacks. -/
private lemma pullbackGlobalSections_app_eq {W : Scheme.{u}} (g : W ⟶ X) {F G : X.Modules}
    (φ : F ⟶ G) {y : Γ(F, ⊤)} {z : Γ((Scheme.Modules.pullback g).obj F, ⊤)}
    (h : pullbackGlobalSections g F y = z) :
    pullbackGlobalSections g G (φ.app ⊤ y) =
      ((Scheme.Modules.pullback g).map φ).app ⊤ z :=
  (pullbackGlobalSections_natural g φ y).trans
    (congrArg (fun z => ((Scheme.Modules.pullback g).map φ).app ⊤ z) h)

/-- A module split off a finite family of complete modules by a total decomposition of its
identity is itself complete. -/
private theorem isInfinitesimalSectionsComplete_of_total {κ : Type*} [Fintype κ]
    (F : κ → X.Modules) (P : X.Modules) (p : ∀ j, P ⟶ F j) (q : ∀ j, F j ⟶ P)
    (htotal : ∑ j, p j ≫ q j = 𝟙 P)
    (h : ∀ j, IsInfinitesimalSectionsComplete i (F j)) :
    IsInfinitesimalSectionsComplete i P := by
  intro x hx
  have H := fun j => h j
    (fun n => ((Scheme.Modules.pullback
      (nthInfinitesimalNeighbourhoodι i n)).map (p j)).app ⊤ (x n))
    (pullbackMap_app_compatible i (p j) x hx)
  choose t ht htuniq using H
  refine ⟨∑ j, (q j).app ⊤ (t j), fun n => ?_, fun y hy => ?_⟩
  · refine (map_sum (ConcreteCategory.hom
      (pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) P))
      (fun j => (q j).app ⊤ (t j)) Finset.univ).trans ?_
    refine (Finset.sum_congr rfl (fun j _ =>
      (pullbackGlobalSections_app_eq _ (q j) (ht j n)).trans
        (appMap_comp _ (p j) (q j) (x n)))).trans ?_
    exact (appMap_sum _ Finset.univ (fun j => p j ≫ q j) (x n)).symm.trans
      ((appMap_eq_of_eq _ _ _ htotal (x n)).trans (appMap_id _ (x n)))
  · have hpy : ∀ j, (p j).app ⊤ y = t j := fun j => htuniq j ((p j).app ⊤ y) (fun n =>
      pullbackGlobalSections_app_eq _ (p j) (hy n))
    calc y = Scheme.Modules.Hom.app (𝟙 P) ⊤ y := rfl
      _ = (∑ j, p j ≫ q j).app ⊤ y :=
          congrArg (fun χ => Scheme.Modules.Hom.app χ ⊤ y) htotal.symm
      _ = ∑ j, (p j ≫ q j).app ⊤ y := app_sum ⊤ Finset.univ (fun j => p j ≫ q j) y
      _ = ∑ j, (q j).app ⊤ (t j) :=
          Finset.sum_congr rfl (fun j _ => congrArg (fun z => (q j).app ⊤ z) (hpy j))

/-- Section completeness passes to a retract. -/
public theorem isInfinitesimalSectionsComplete_of_retract {F G : X.Modules} (s : F ⟶ G)
    (r : G ⟶ F) (hsr : s ≫ r = 𝟙 F) (hG : IsInfinitesimalSectionsComplete i G) :
    IsInfinitesimalSectionsComplete i F :=
  isInfinitesimalSectionsComplete_of_total i (fun _ : Unit => G) F (fun _ => s) (fun _ => r)
    (by simpa using hsr) (fun _ => hG)

/-- The zero module is section complete. -/
public theorem isInfinitesimalSectionsComplete_zero :
    IsInfinitesimalSectionsComplete i (0 : X.Modules) :=
  isInfinitesimalSectionsComplete_of_total i (fun j : Empty => j.elim) 0 (fun j => j.elim)
    (fun j => j.elim)
    (by
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      exact (isZero_zero X.Modules).eq_of_src _ _)
    (fun j => j.elim)

/-- Section completeness is stable under binary biproducts. -/
public theorem isInfinitesimalSectionsComplete_biprod {F G : X.Modules}
    (hF : IsInfinitesimalSectionsComplete i F) (hG : IsInfinitesimalSectionsComplete i G) :
    IsInfinitesimalSectionsComplete i (F ⊞ G) :=
  isInfinitesimalSectionsComplete_of_total i (fun c : Bool => cond c F G) (F ⊞ G)
    (fun c => Bool.rec (motive := fun c => (F ⊞ G) ⟶ cond c F G) biprod.snd biprod.fst c)
    (fun c => Bool.rec (motive := fun c => cond c F G ⟶ (F ⊞ G)) biprod.inr biprod.inl c)
    (by rw [Fintype.sum_bool]; exact biprod.total)
    (fun c => Bool.rec (motive := fun c => IsInfinitesimalSectionsComplete i (cond c F G)) hG hF c)

/-- Section completeness is stable under finite biproducts, in bicone form. -/
public theorem isInfinitesimalSectionsComplete_bicone_pt {ι : Type u} [Finite ι]
    {F : ι → X.Modules} (b : CategoryTheory.Limits.Bicone F) (hb : b.IsBilimit)
    (h : ∀ j, IsInfinitesimalSectionsComplete i (F j)) :
    IsInfinitesimalSectionsComplete i b.pt := by
  have := Fintype.ofFinite ι
  exact isInfinitesimalSectionsComplete_of_total i F b.pt b.π b.ι (IsBilimit.total hb) h

/-- Section completeness is stable under finite biproducts. -/
public theorem isInfinitesimalSectionsComplete_biproduct {ι : Type u} [Finite ι]
    (F : ι → X.Modules) (h : ∀ j, IsInfinitesimalSectionsComplete i (F j)) :
    IsInfinitesimalSectionsComplete i (CategoryTheory.Limits.biproduct F) :=
  isInfinitesimalSectionsComplete_bicone_pt i (biproduct.bicone F) (biproduct.isBilimit F) h

/-- Section completeness is inherited by a module realised as the sections kernel of a map
between complete modules. -/
public theorem isInfinitesimalSectionsComplete_of_sectionsKernel {E A B : X.Modules}
    (ψ : E ⟶ A) (b : A ⟶ B) (hzero : ψ ≫ b = 0)
    (hinj : Function.Injective (fun t : Γ(E, (⊤ : X.Opens)) => ψ.app ⊤ t))
    (hex : ∀ u : Γ(A, (⊤ : X.Opens)), b.app ⊤ u = 0 → ∃ t : Γ(E, (⊤ : X.Opens)), ψ.app ⊤ t = u)
    (hmono : ∀ n : ℕ, Function.Injective
      (fun t : Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj E,
          (⊤ : (nthInfinitesimalNeighbourhood i n).Opens)) =>
        ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).map ψ).app ⊤ t))
    (hA : IsInfinitesimalSectionsComplete i A) (hB : IsInfinitesimalSectionsComplete i B) :
    IsInfinitesimalSectionsComplete i E := by
  intro s hs
  obtain ⟨u, hu, huniq⟩ := hA
    (fun n => ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).map ψ).app ⊤ (s n))
    (pullbackMap_app_compatible i ψ s hs)
  obtain ⟨w, -, hwuniq⟩ := hB
    (fun n => (0 : Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj B, ⊤)))
    (fun n m h => map_zero (ConcreteCategory.hom
      (pullbackSectionsMap B (nthInfinitesimalNeighbourhoodTransition i h))))
  have hbu : b.app ⊤ u = 0 :=
    (hwuniq (b.app ⊤ u) (fun n =>
      (pullbackGlobalSections_app_eq _ b (hu n)).trans
        ((appMap_comp _ ψ b (s n)).trans
          ((appMap_eq_of_eq _ _ _ hzero (s n)).trans (appMap_zero _ (s n)))))).trans
      (hwuniq 0 (fun n => map_zero (ConcreteCategory.hom
        (pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) B)))).symm
  obtain ⟨t, htu⟩ := hex u hbu
  refine ⟨t, fun n => hmono n ?_, fun y hy => ?_⟩
  · exact (pullbackGlobalSections_natural _ ψ t).symm.trans
      ((congrArg (fun z => pullbackGlobalSections
        (nthInfinitesimalNeighbourhoodι i n) A z) htu).trans (hu n))
  · exact hinj ((huniq (ψ.app ⊤ y) (fun n =>
      pullbackGlobalSections_app_eq _ ψ (hy n))).trans htu.symm)

end Stacks.Algebraization

end

