module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangles

/-!
# Deligne systems and the one-degree truncations of an inverse system

Let `j^* : 𝒟 ⥤ 𝒞` be a triangulated functor with a Deligne system assignment, and let `t` be a
`t`-structure on `𝒟`. An inverse system `(K_n)` of `𝒟` whose terms live in the degree range
`[a, b]` is pro-isomorphic to a Deligne system as soon as each of its one-degree truncations
`τ^{≥p}τ^{≤p}K_n` is, for `a ≤ p ≤ b`.

This is the implication (2) ⇒ (1) of Stacks 0G4S. In the situation of that tag, `𝒟` is
`D^b_{Coh}(𝒪_X)` for an open immersion `j : U → X` of Noetherian schemes, the one-degree
truncation of `K_n` is the cohomology sheaf `H^p(K_n)` placed in degree `p`, and the Deligne
systems concentrated in a single degree are exactly the systems `(𝓘^n𝓕)[-p]` of a coherent
module `𝓕`; so the hypothesis here is the source's condition (2).

The proof is the source's: induction on `b - a`. For `a = b` the system is isomorphic to its own
one-degree truncation. For `a < b` the `t`-structure triangles
`τ^{≤a}K_n ⟶ K_n ⟶ τ^{≥a+1}K_n ⟶ (τ^{≤a}K_n)[1]` of Stacks 08J5 form an inverse system of
distinguished triangles whose outer two systems satisfy the hypothesis in the shorter ranges
`[a, a]` and `[a + 1, b]`, so Stacks 0G4Q applies to the middle one.

## Main results

* `CategoryTheory.DeligneSystemValues.proIsoDeligne_of_truncGELE`: Stacks 0G4S, (2) ⇒ (1).

### No unrestricted `@[stacks 0G4S]`

Only (2) ⇒ (1) is proved here. The converse (1) ⇒ (2) is, in the source, a one-line appeal to
Stacks 0G4R: a Deligne system is `(𝓘^n𝓕^•)` for a bounded complex `𝓕^•` of coherent modules,
and 0G4R says its cohomology systems `(H^p(𝓘^n𝓕^•))` are pro-isomorphic to `(𝓘^n𝓕)` for coherent
`𝓕`. Stacks 0G4R is **available**: the transition maps are
`AlgebraicGeometry.idealPowerComplexSystem`, and its Artin-Rees content — the uniform constant
`c`, the maps back and the two composites — is
`Stacks.Duality.cohomologyIdealPowers_proIsomorphic`, packaged as a `ProIso` of the two inverse
sequences by `Stacks.Duality.cohomologyIdealPowersProIso`. Both are proved for schemes
directly, without globalizing the affine case Stacks 0G3K
(`InverseSequence.homologyIdealPowers_proIsomorphic`). What (1) ⇒ (2) still needs is the
identification of the one-degree truncations of the system in `D^b_{Coh}(𝒪_X)` with those
cohomology sheaves placed in a single degree.

Both implications are stated here for a `DeligneSystemValues` assignment and a `t`-structure
supplied as data, as Stacks 0G4Q already is in this directory. `D^b_{Coh}(𝒪_X)` now carries the
`t`-structure — `AlgebraicGeometry.isTriangulated_boundedCoherentDerived` makes
`BoundedCoherentDerived X` pretriangulated and `AlgebraicGeometry.boundedCoherentTStructure` is
the induced `t`-structure — so the `t`-structure argument can be instantiated there; the
assignment cannot, because the existence half of Stacks 0G4L, which produces it, is not
formalized.

## References

* [Stacks Project, Tag 0G4S](https://stacks.math.columbia.edu/tag/0G4S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated Opposite

universe v u u'

namespace CategoryTheory

section Transport

variable {𝒟 : Type u} [Category.{v} 𝒟] {𝒞 : Type u'} [Category.{v} 𝒞]

/-- An isomorphism of inverse sequences induces an isomorphism of their pro-objects. -/
public def ProSeq.ofIsoOfNatIso {F G : ℕᵒᵖ ⥤ 𝒟} (e : F ≅ G) : ProSeq.of F ≅ ProSeq.of G :=
  ProSeq.isoOfSeqHomColimIso
    (HasColimit.isoOfNatIso (Functor.isoWhiskerRight (NatIso.op e.symm) coyoneda))

/-- Being pro-isomorphic to a Deligne system only depends on the isomorphism class of the
inverse sequence. -/
public lemma DeligneSystemValues.proIsoDeligne_of_natIso {jstar : 𝒟 ⥤ 𝒞}
    (A : DeligneSystemValues jstar) {F G : ℕᵒᵖ ⥤ 𝒟} (e : F ≅ G) (h : A.ProIsoDeligne G) :
    A.ProIsoDeligne F := by
  obtain ⟨L, ⟨i⟩⟩ := h
  exact ⟨L, ⟨ProSeq.ofIsoOfNatIso e ≪≫ i⟩⟩

end Transport

section Truncation

variable {𝒟 : Type u} [Category.{v} 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] [IsTriangulated 𝒟]
  {𝒞 : Type u'} [Category.{v} 𝒞] [Preadditive 𝒞] [HasZeroObject 𝒞] [HasShift 𝒞 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]

namespace Triangulated.TStructure

/-- Truncating below degree `a` does not change the one-degree truncation in degree `a`:
`τ^{≥a}τ^{≤a}τ^{≤a} ≅ τ^{≥a}τ^{≤a}`. -/
public def truncLECompTruncGELEIso (t : TStructure 𝒟) (a : ℤ) :
    t.truncLE a ⋙ t.truncGELE a a ≅ t.truncGELE a a := by
  have key : ∀ X : 𝒟,
      IsIso ((Functor.whiskerRight (t.truncLEι a) (t.truncGELE a a)).app X) := fun X =>
    inferInstanceAs (IsIso ((t.truncGE a).map ((t.truncLE a).map ((t.truncLEι a).app X))))
  have : IsIso (Functor.whiskerRight (t.truncLEι a) (t.truncGELE a a)) :=
    NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerRight (t.truncLEι a) (t.truncGELE a a))

/-- Truncating above degree `b` does not change the one-degree truncation in a degree `p ≥ b`:
`τ^{≥p}τ^{≤p}τ^{≥b} ≅ τ^{≥p}τ^{≤p}`. -/
public def truncGECompTruncGELEIso (t : TStructure 𝒟) {b p : ℤ} (h : b ≤ p) :
    t.truncGE b ⋙ t.truncGELE p p ≅ t.truncGELE p p := by
  have key : ∀ X : 𝒟, IsIso ((Functor.whiskerRight (t.truncGEπ b) (t.truncGE p)).app X) :=
    fun X => t.isIso_truncGE_map_truncGEπ_app p b h X
  have : IsIso (Functor.whiskerRight (t.truncGEπ b) (t.truncGE p)) :=
    NatIso.isIso_of_isIso_app _
  exact Functor.isoWhiskerRight (t.truncGELEIsoLEGE b p).symm (t.truncGE p) ≪≫
    Functor.isoWhiskerLeft (t.truncLE p)
      (asIso (Functor.whiskerRight (t.truncGEπ b) (t.truncGE p))).symm

/-- An inverse sequence concentrated in the single degree `a` is isomorphic to its own
one-degree truncation `τ^{≥a}τ^{≤a}`. -/
public def truncGELESelfIso (t : TStructure 𝒟) (K : ℕᵒᵖ ⥤ 𝒟) (a : ℤ)
    (hGE : ∀ n, t.IsGE (K.obj n) a) (hLE : ∀ n, t.IsLE (K.obj n) a) :
    K ≅ K ⋙ t.truncGELE a a := by
  have hβ : ∀ n, IsIso ((Functor.whiskerLeft K (t.truncGEπ a)).app n) := fun n => by
    have := hGE n
    exact inferInstanceAs (IsIso ((t.truncGEπ a).app (K.obj n)))
  have hγ : ∀ n,
      IsIso ((Functor.whiskerLeft K (Functor.whiskerRight (t.truncLEι a) (t.truncGE a))).app n) :=
    fun n => by
      have := hLE n
      exact inferInstanceAs (IsIso ((t.truncGE a).map ((t.truncLEι a).app (K.obj n))))
  have : IsIso (Functor.whiskerLeft K (t.truncGEπ a)) := NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerLeft K (Functor.whiskerRight (t.truncLEι a) (t.truncGE a))) :=
    NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerLeft K (t.truncGEπ a)) ≪≫
    (asIso (Functor.whiskerLeft K
      (Functor.whiskerRight (t.truncLEι a) (t.truncGE a)))).symm

end Triangulated.TStructure

omit [IsTriangulated 𝒟] [Preadditive 𝒞] [HasZeroObject 𝒞] [HasShift 𝒞 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞] in
/-- An inverse sequence concentrated in a single degree is pro-isomorphic to a Deligne system
as soon as its one-degree truncation is. This is the base case `a = b` of Stacks 0G4S (2) ⇒ (1),
where the source says that (1) holds "essentially by assumption". -/
public lemma DeligneSystemValues.proIsoDeligne_of_single {jstar : 𝒟 ⥤ 𝒞}
    (A : DeligneSystemValues jstar) (t : TStructure 𝒟) (K : ℕᵒᵖ ⥤ 𝒟) (a : ℤ)
    (hGE : ∀ n, t.IsGE (K.obj n) a) (hLE : ∀ n, t.IsLE (K.obj n) a)
    (H : A.ProIsoDeligne (K ⋙ t.truncGELE a a)) : A.ProIsoDeligne K :=
  A.proIsoDeligne_of_natIso (t.truncGELESelfIso K a hGE hLE) H

/-- The induction on the length of the degree range underlying Stacks 0G4S (2) ⇒ (1): if the
terms of `(K_n)` lie in `[a, a + k]` and every one-degree truncation in that range is
pro-isomorphic to a Deligne system, then so is `(K_n)`. -/
public lemma DeligneSystemValues.proIsoDeligne_of_truncGELE_aux {jstar : 𝒟 ⥤ 𝒞} [jstar.Additive]
    [jstar.CommShift ℤ] [jstar.IsTriangulated] (A : DeligneSystemValues jstar)
    (t : TStructure 𝒟) :
    ∀ (k : ℕ) (a b : ℤ), b = a + k → ∀ K : ℕᵒᵖ ⥤ 𝒟, (∀ n, t.IsGE (K.obj n) a) →
      (∀ n, t.IsLE (K.obj n) b) →
      (∀ p : ℤ, a ≤ p → p ≤ b → A.ProIsoDeligne (K ⋙ t.truncGELE p p)) →
      A.ProIsoDeligne K := by
  intro k
  induction k with
  | zero =>
    intro a b hb K hGE hLE H
    have hba : b = a := by simpa using hb
    subst hba
    exact A.proIsoDeligne_of_single t K b hGE hLE (H b le_rfl le_rfl)
  | succ k ih =>
    intro a b hb K hGE hLE H
    have hab : a + 1 ≤ b := by
      rw [hb]; push_cast; omega
    have h₁ : A.ProIsoDeligne (K ⋙ t.truncLE a) := by
      refine A.proIsoDeligne_of_single t (K ⋙ t.truncLE a) a (fun n => ?_) (fun n => ?_) ?_
      · have := hGE n
        exact inferInstanceAs (t.IsGE ((t.truncLE a).obj (K.obj n)) a)
      · exact inferInstanceAs (t.IsLE ((t.truncLE a).obj (K.obj n)) a)
      · exact A.proIsoDeligne_of_natIso
          (Functor.isoWhiskerLeft K (t.truncLECompTruncGELEIso a))
          (H a le_rfl (by omega))
    have h₃ : A.ProIsoDeligne (K ⋙ t.truncGE (a + 1)) := by
      refine ih (a + 1) b (by rw [hb]; push_cast; omega) (K ⋙ t.truncGE (a + 1))
        (fun n => ?_) (fun n => ?_) (fun p hp hp' => ?_)
      · exact inferInstanceAs (t.IsGE ((t.truncGE (a + 1)).obj (K.obj n)) (a + 1))
      · have := hLE n
        exact inferInstanceAs (t.IsLE ((t.truncGE (a + 1)).obj (K.obj n)) b)
      · exact A.proIsoDeligne_of_natIso
          (Functor.isoWhiskerLeft K (t.truncGECompTruncGELEIso hp))
          (H p (by omega) hp')
    exact A.proIsoDeligne_π₂ (K ⋙ t.triangleLEGE a (a + 1) rfl)
      (fun n => t.triangleLEGE_distinguished a (a + 1) rfl (K.obj n)) h₁ h₃

/-- **Stacks Project, Tag 0G4S**, the implication (2) ⇒ (1). Let `j^* : 𝒟 ⥤ 𝒞` be a triangulated
functor with a Deligne system assignment, `t` a `t`-structure on `𝒟`, and `(K_n)` an inverse
sequence of `𝒟` whose terms lie in the degree range `[a, b]`. If each one-degree truncation
`τ^{≥p}τ^{≤p}K_n`, for `a ≤ p ≤ b`, is pro-isomorphic to a Deligne system, then `(K_n)` is. -/
@[stacks 0G4S "(2) implies (1) only, and with (2) in the equivalent form that each one-degree \
truncation system (τ^{≥p}τ^{≤p}K_n) is pro-isomorphic to a Deligne system, for a Deligne-system \
assignment and a t-structure supplied as data. (1) implies (2) is not proved: it is Stacks 0G4R, \
whose Artin-Rees content the library does not have."]
public theorem DeligneSystemValues.proIsoDeligne_of_truncGELE {jstar : 𝒟 ⥤ 𝒞} [jstar.Additive]
    [jstar.CommShift ℤ] [jstar.IsTriangulated] (A : DeligneSystemValues jstar)
    (t : TStructure 𝒟) {a b : ℤ} (hab : a ≤ b) (K : ℕᵒᵖ ⥤ 𝒟)
    (hGE : ∀ n, t.IsGE (K.obj n) a) (hLE : ∀ n, t.IsLE (K.obj n) b)
    (H : ∀ p : ℤ, a ≤ p → p ≤ b → A.ProIsoDeligne (K ⋙ t.truncGELE p p)) :
    A.ProIsoDeligne K :=
  A.proIsoDeligne_of_truncGELE_aux t (b - a).toNat a b (by omega) K hGE hLE H

end Truncation

end CategoryTheory

end
