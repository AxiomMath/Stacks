module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermGlobal.Local
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermGlobal.Glue

/-!
# The determinant of a two-term perfect complex on a scheme

Let `X` be a scheme and `K` a perfect object of `D(𝒪_X)` of Tor amplitude in `[-1, 0]`. For every
affine open `V`, the restriction of `K` to `V` is the sheaf associated with a perfect complex
`M_V` of `Γ(X, V)`-modules of Tor amplitude in `[-1, 0]`, which has a determinant `det(M_V)`, an
invertible `Γ(X, V)`-module (More on Algebra, Section 0FJI). For affine opens `W ⊆ V` the
identification `Γ(X, W) ⊗ᴸ M_V ≅ M_W` induces `det(M_V) → det(M_W)`, which exhibits `det(M_W)` as
`Γ(X, W) ⊗ det(M_V)`. These glue to an `𝒪_X`-module `det(K)` whose sections over an affine open
`V` are `det(M_V)`. When `K` has rank zero, the canonical elements `δ(M_V)` glue to the global
section `δ(K)`. This is the construction of the proof of Stacks 0FJX carried out directly; it is
identified with the value of the determinant functor
`AlgebraicGeometry.DeterminantTwoTerm.determinantFunctor`, and `δ(K)` with its canonical section
`AlgebraicGeometry.DeterminantTwoTerm.determinantSection`, by
`AlgebraicGeometry.DeterminantTwoTerm.detModuleIso`
(`StacksFrontier/AlgebraicGeometry/DeterminantTwoTermGlobal/GlobalDetIso.lean`).

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.detSystem`: the system `V ↦ det(M_V)`.
* `AlgebraicGeometry.DeterminantTwoTerm.detModule`: the `𝒪_X`-module `det(K)`.
* `AlgebraicGeometry.DeterminantTwoTerm.IsRankZero`: `K` has rank zero.
* `AlgebraicGeometry.DeterminantTwoTerm.deltaSection`: the global section `δ(K)`.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.detSectionsEquiv`: `Γ(det(K), V) ≅ det(M_V)` for `V`
  affine.
* `AlgebraicGeometry.DeterminantTwoTerm.detSectionsEquiv_deltaSection`: `δ(K)` restricts on `V`
  to `δ(M_V)`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite TwoTermDeterminant
open AlgebraicGeometry.StandardModel

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}} (K : PerfectTwoTermAmplitude X)

/-- The map of local determinants along a ring map depends only on the ring map, not on the
proofs of compatibility with the maps to `X`. -/
theorem localDetMap_congr {A B : CommRingCat.{u}} {g g' : A ⟶ B} (hg : g = g') (u : Spec A ⟶ X)
    (u' : Spec B ⟶ X) (h : Spec.map g ≫ u = u') (h' : Spec.map g' ≫ u = u')
    (x : localDet K u) : localDetMap K g u u' h x = localDetMap K g' u u' h' x := by
  subst hg
  rfl

/-- Restriction of sections of the structure sheaf from `V` to `W` and then to `W'` is
restriction from `V` to `W'`. -/
theorem presheaf_map_comp {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) :
    X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op =
      X.presheaf.map (homOfLE (h'.trans h)).op := by
  rw [← Functor.map_comp]
  rfl

/-- An identity of local determinants: the map along a ring map which is the identity on
elements is the identity. -/
theorem localDetMap_eq_self_of_idem {A : CommRingCat.{u}} (g : A ⟶ A) (hg : g ≫ g = g)
    (hg' : ∀ a, g a = a) (u : Spec A ⟶ X) (h : Spec.map g ≫ u = u) (x : localDet K u) :
    localDetMap K g u u h x = x := by
  have hh : Spec.map (g ≫ g) ≫ u = u := by rw [hg, h]
  have hcomp := localDetMap_comp K g g u u u h h hh x
  rw [localDetMap_congr K hg u u hh h] at hcomp
  -- the map is injective, being a base change along a ring map which is the identity on elements
  let idg : localDet K u →ₛₗ[g.hom] localDet K u :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r y => by rw [hg']; rfl }
  obtain ⟨k, hk, -⟩ := isBaseChangeAlong_localDetMap K g u u h (localDet K u) idg
  have hinj : Function.Injective (localDetMap K g u u h) := fun a b hab => by
    have ha := LinearMap.congr_fun hk a
    have hb := LinearMap.congr_fun hk b
    simp only [LinearMap.comp_apply] at ha hb
    exact (ha.symm.trans (congrArg k hab)).trans hb
  exact hinj hcomp.symm

/-- **The system of local determinants on the affine opens of `X`.** -/
def detSystem : AffineLineSystem X where
  obj V := localDet K V.2.fromSpec
  map {V W} h := localDetMap K (X.presheaf.map (homOfLE h).op) V.2.fromSpec W.2.fromSpec
    (IsAffineOpen.map_fromSpec _ _ _)
  map_id V x := localDetMap_eq_self_of_idem K _ (by rw [presheaf_map_comp])
    (fun a => AffineLineSystem.map_presheaf_id _ a) _ _ x
  map_map {V W W'} h h' x := by
    have hh : Spec.map (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op) ≫
        V.2.fromSpec = W'.2.fromSpec := by
      rw [presheaf_map_comp]
      exact IsAffineOpen.map_fromSpec _ _ _
    rw [← localDetMap_comp K _ _ _ _ _ _ _ hh]
    exact localDetMap_congr K (presheaf_map_comp h h') _ _ _ _ x
  isBaseChange h := isBaseChangeAlong_localDetMap K _ _ _ _

/-- The determinant `det(M_V)` is an invertible `Γ(X, V)`-module. -/
instance (V : X.affineOpens) : Module.Invertible Γ(X, V) ((detSystem K).obj V) :=
  ((det Γ(X, V)).obj ⟨localComplex K V.2.fromSpec⟩).of.property

/-- The determinant `det(M_V)` is a finite `Γ(X, V)`-module. -/
instance (V : X.affineOpens) : Module.Finite Γ(X, V) ((detSystem K).obj V) := inferInstance

/-- The determinant `det(M_V)` is a projective `Γ(X, V)`-module. -/
instance (V : X.affineOpens) : Module.Projective Γ(X, V) ((detSystem K).obj V) := inferInstance

/-- **The determinant `det(K)`**, an `𝒪_X`-module, glued directly from the local determinants of
More on Algebra, Section 0FJI. It is isomorphic to the value of the determinant functor of Stacks
0FJX by `detModuleIso`. -/
def detModule : X.Modules :=
  (detSystem K).toModules

/-- The determinant `det(K)` is a quasi-coherent `𝒪_X`-module. -/
instance : (detModule K).IsQuasicoherent :=
  (detSystem K).isQuasicoherent_toModules

/-- **The determinant on an affine open is the determinant of More on Algebra, Section 0FJI** of
the local avatar of `K`. -/
def detSectionsEquiv (V : X.affineOpens) :
    Γ(detModule K, V) ≃ₗ[Γ(X, V)] localDet K V.2.fromSpec :=
  (detSystem K).sectionsEquiv V

/-- For affine opens `W ⊆ V`, the identifications `Γ(det(K), V) ≅ det(M_V)` and
`Γ(det(K), W) ≅ det(M_W)` carry restriction of sections to the map `det(M_V) → det(M_W)`. -/
theorem detSectionsEquiv_restrict {V W : X.affineOpens} (h : (W : X.Opens) ≤ V)
    (a : Γ(detModule K, V)) :
    detSectionsEquiv K W ((detModule K).presheaf.map (homOfLE h).op a) =
      localDetMap K (X.presheaf.map (homOfLE h).op) V.2.fromSpec W.2.fromSpec
        (IsAffineOpen.map_fromSpec _ _ _) (detSectionsEquiv K V a) :=
  (detSystem K).sectionsEquiv_restrict h a

/-- **Rank zero.** `K` has rank zero when its derived pullback to every affine scheme over `X` has
rank zero, that is, admits a two-term finite-projective presentation whose two terms have the same
rank at every prime. It is equivalent to `IsRankZeroOn`, rank zero on the affine charts
(`isRankZero_iff_isRankZeroOn`). -/
def IsRankZero : Prop :=
  ∀ (A : CommRingCat.{u}) (u : Spec A ⟶ X), IsLocallyRankZero K u

/-- **The canonical global section `δ(K)`** of the determinant of a rank-zero object: the
canonical elements of More on Algebra, Section 0FJI of the local avatars, glued. -/
def deltaSection (hK : IsRankZero K) : Γ(detModule K, ⊤) :=
  ((detSystem K).sec ⊤).symm
    ⟨fun V => delta (localComplex K V.1.2.fromSpec) (hK _ _), fun _ _ _ =>
      localDetMap_delta K _ _ _ _ _ _⟩

/-- For `K` of rank zero and `V` an affine open, the restriction of `δ(K)` to `V` corresponds to
the canonical element `δ(M_V)` under `Γ(det(K), V) ≅ det(M_V)`. -/
theorem detSectionsEquiv_deltaSection (hK : IsRankZero K) (V : X.affineOpens) :
    detSectionsEquiv K V ((detModule K).presheaf.map (homOfLE le_top).op (deltaSection K hK)) =
      delta (localComplex K V.2.fromSpec) (hK _ _) :=
  rfl

end AlgebraicGeometry.DeterminantTwoTerm

end
