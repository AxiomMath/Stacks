module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.AlgebraicGeometry.MorphismsIntoProj
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Trivialize

/-!
# Uniqueness of a morphism into `Proj` and of its trivialization

Let `S` be a graded ring, `X = Proj(S)`, let `d ≥ 1` and let `U_d = ⋃_{f ∈ S_d} D₊(f) ⊆ X`. Let
`Y` be a scheme, `L` an invertible `𝒪_Y`-module and `ψ : S^{(d)} → Γ_*(Y, L)` a graded ring map
whose degree-`d` part generates `L`. This file proves that a pair `(φ, α)` consisting of a
morphism `φ : Y ⟶ U_d` and an isomorphism `α : φ⁎𝒪_{U_d}(d) ≅ L` compatible with `ψ` is unique.

## Main results

* `Stacks.AlgebraicGeometry.ProjSectionsUnique.eq_of_smul_restrict_eq`: if a section of an
  invertible module over an open inside the nonvanishing open of `t` is written as a multiple of
  `t` in two ways, the two scalars agree.
* `Stacks.AlgebraicGeometry.ProjSectionsUnique.eq_of_appLE_eq`: two morphisms `φ, φ' : Y ⟶ U_d`
  with the same preimage `W_f` of each `D₊(f)`, `f ∈ S_d`, and with the same induced ring map
  `Γ(X, D₊(f)) ⟶ Γ(Y, W_f)`, are equal.
* `Stacks.AlgebraicGeometry.ProjSectionsUnique.eq_of_appLE_eq_on_away`: the same with the ring maps
  compared only on the fractions `a/f^n`.
* `Stacks.AlgebraicGeometry.ProjSectionsUnique.eq_of_smul_appLE_eq`: the same again, from the
  identity `ψ(a)|_{Y_s} = φ^♯(a/f^n) · (s^n)|_{Y_s}` for `φ` and for `φ'`.
* `Stacks.AlgebraicGeometry.ProjSectionsUnique.hom_ext_of_spansOver` and
  `Stacks.AlgebraicGeometry.ProjSectionsUnique.hom_ext_of_iSup_nonvanishingOpen_eq_top`: two
  morphisms out of a sheaf of modules that agree on a family of global sections generating it are
  equal; for an invertible module, the sections generate it when their nonvanishing opens cover
  `Y`.
* `Stacks.AlgebraicGeometry.ProjSectionsUnique.iso_eq_of_app_eq`: two isomorphisms `M ≅ L` carrying
  a fixed family of sections of `M` to a family of sections generating `L` are equal.
* `Stacks.AlgebraicGeometry.ProjSectionsUnique.pair_eq`: the pair `(φ, α)` is determined, as an
  equality in the type of such pairs.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Equation 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open HomogeneousLocalization

namespace Stacks.AlgebraicGeometry.ProjSectionsUnique

universe u w

/-! ### Morphisms of module sheaves and generating global sections -/

section Generation

variable {Y : Scheme.{u}}

/-- Restriction of a morphism of `𝒪_Y`-modules commutes with restriction of sections. -/
theorem map_app {M N : Y.Modules} (u : M ⟶ N) {V W : Y.Opens} (hWV : W ≤ V) (x : Γ(M, V)) :
    N.presheaf.map (homOfLE hWV).op (u.app V x) =
      u.app W (M.presheaf.map (homOfLE hWV).op x) := by
  simpa using (ConcreteCategory.congr_hom (u.mapPresheaf.naturality (homOfLE hWV).op) x).symm

/-- A global section `s` of an `𝒪_Y`-module `M` spans `M` over an open `G` when every section of
`M` over an open contained in `G` is a scalar multiple of the restriction of `s`. -/
def SpansOver (M : Y.Modules) (s : Γ(M, ⊤)) (G : Y.Opens) : Prop :=
  ∀ W : Y.Opens, W ≤ G → ∀ x : Γ(M, W),
    ∃ a : Γ(Y, W), x = a • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s

/-- If opens `G i` cover `Y`, every point lies in one of them. -/
private theorem exists_mem_of_iSup_eq_top {ι : Type*} {G : ι → Y.Opens} (h : ⨆ i, G i = ⊤)
    (p : Y) : ∃ i, p ∈ G i :=
  Opens.mem_iSup.mp (h ▸ Opens.mem_top p)

/-- Two morphisms out of a sheaf of modules that agree on a family of global sections `s i`
spanning it over opens `G i` covering `Y` are equal. -/
theorem hom_ext_of_spansOver {M N : Y.Modules} {ι : Type*} (s : ι → Γ(M, ⊤)) (G : ι → Y.Opens)
    (hcover : ⨆ i, G i = ⊤) (hspan : ∀ i, SpansOver M (s i) (G i)) {u v : M ⟶ N}
    (h : ∀ i, u.app ⊤ (s i) = v.app ⊤ (s i)) : u = v := by
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext x
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨N.presheaf, by exact N.isSheaf⟩ : TopCat.Sheaf _ _)
    (fun i ↦ W ⊓ G i) W (fun i ↦ homOfLE inf_le_left) ?_ _ _ fun i ↦ ?_
  · intro p hp
    obtain ⟨i, hi⟩ := exists_mem_of_iSup_eq_top hcover p
    exact Opens.mem_iSup.mpr ⟨i, hp, hi⟩
  · obtain ⟨a, ha⟩ := hspan i (W ⊓ G i) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op x)
    rw [map_app u inf_le_left x, map_app v inf_le_left x, ha, u.app_smul, v.app_smul,
      ← map_app u (le_top : W ⊓ G i ≤ ⊤), ← map_app v (le_top : W ⊓ G i ≤ ⊤), h i]

variable (Y) in
/-- A global section of an invertible module spans it on its nonvanishing open. -/
theorem spansOver_nonvanishingOpen (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    (s : Γ(M, ⊤)) : SpansOver M s (Stacks.NonvanishingOpen.nonvanishingOpen Y M s) :=
  fun _ hW x ↦
    let ⟨a, ha⟩ := (Stacks.NonvanishingSpelling.bijective_smul Y M s hW).2 x
    ⟨a, ha.symm⟩

/-- Two morphisms out of an invertible module that agree on a family of global sections whose
nonvanishing opens cover `Y` are equal. -/
theorem hom_ext_of_iSup_nonvanishingOpen_eq_top {M N : Y.Modules}
    [Stacks.Ample.IsInvertibleModule Y M] {ι : Type*} (s : ι → Γ(M, ⊤))
    (hcover : ⨆ i, Stacks.NonvanishingOpen.nonvanishingOpen Y M (s i) = ⊤) {u v : M ⟶ N}
    (h : ∀ i, u.app ⊤ (s i) = v.app ⊤ (s i)) : u = v :=
  hom_ext_of_spansOver s _ hcover (fun i ↦ spansOver_nonvanishingOpen Y M (s i)) h

/-- Two isomorphisms `α, α' : M ≅ L` that send a fixed family of global sections `m i` of `M` to
one and the same family `t i` of global sections of `L` whose nonvanishing opens cover `Y` are
equal. -/
theorem iso_eq_of_app_eq {M L : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L] {ι : Type*}
    {m : ι → Γ(M, ⊤)} {t : ι → Γ(L, ⊤)}
    (hcover : ⨆ i, Stacks.NonvanishingOpen.nonvanishingOpen Y L (t i) = ⊤) (α α' : M ≅ L)
    (hα : ∀ i, α.hom.app ⊤ (m i) = t i) (hα' : ∀ i, α'.hom.app ⊤ (m i) = t i) : α = α' := by
  have key : ∀ (β : M ≅ L), (∀ i, β.hom.app ⊤ (m i) = t i) → ∀ i, β.inv.app ⊤ (t i) = m i := by
    intro β hβ i
    rw [← hβ i, ← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, β.hom_inv_id]
    simp
  exact Iso.ext (Iso.inv_eq_inv α α' |>.mp <| hom_ext_of_iSup_nonvanishingOpen_eq_top t hcover
    fun i ↦ by rw [key α hα i, key α' hα' i])

end Generation

/-! ### The trivialization step -/

section Trivialize

variable {Y : Scheme.{u}}

/-- If one and the same section of an invertible `𝒪_Y`-module `M`, over an open `V` inside the
nonvanishing open of a global section `t`, is written as `x · t|_V` and as `y · t|_V`, then
`x = y`. -/
theorem eq_of_smul_restrict_eq (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    (t : Γ(M, ⊤)) {V : Y.Opens} (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen Y M t)
    {c : Γ(M, V)} {x y : Γ(Y, V)}
    (hx : c = x • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t)
    (hy : c = y • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t) : x = y :=
  (Stacks.NonvanishingSpelling.bijective_smul Y M t hV).1 (hx.symm.trans hy)

end Trivialize

/-! ### The morphisms agree -/

section Morphism

open Stacks.AlgebraicGeometry.MorphismsIntoProj

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : Scheme.{u}} {d : ℕ}

/-- The preimages under a morphism `Y ⟶ U_d` of the standard opens `D₊(f)`, `f ∈ S_d`, cover
`Y`. -/
theorem iSup_preimage_basicOpen_eq_top (φ : Y ⟶ (degreeOpen 𝒜 d).toScheme) :
    ⨆ f : 𝒜 d, toProj 𝒜 φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) = ⊤ := by
  simp only [toProj, Scheme.Hom.comp_preimage]
  refine Scheme.Hom.iSup_preimage_eq_top _ ?_
  rw [← Scheme.Hom.preimage_iSup]
  exact (degreeOpen 𝒜 d).ι_preimage_self

/-- Two morphisms `φ, φ' : Y ⟶ U_d` that have the same preimage `W f` of each standard open
`D₊(f)` with `f ∈ S_d`, and that induce the same ring map `Γ(X, D₊(f)) ⟶ Γ(Y, W f)`, are
equal. -/
theorem eq_of_appLE_eq (hd : 0 < d) {φ φ' : Y ⟶ (degreeOpen 𝒜 d).toScheme} {W : 𝒜 d → Y.Opens}
    (hW : ∀ f : 𝒜 d, toProj 𝒜 φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) = W f)
    (hW' : ∀ f : 𝒜 d, toProj 𝒜 φ' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) = W f)
    (happ : ∀ f : 𝒜 d,
      (toProj 𝒜 φ).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) (W f) (hW f).ge =
        (toProj 𝒜 φ').appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) (W f) (hW' f).ge) :
    φ = φ' := by
  have hcover : ⨆ f : 𝒜 d, W f = ⊤ :=
    (iSup_congr fun f ↦ (hW f).symm).trans (iSup_preimage_basicOpen_eq_top 𝒜 φ)
  rw [← cancel_mono (degreeOpen 𝒜 d).ι]
  refine Scheme.hom_ext_of_forall _ _ fun p ↦ ?_
  obtain ⟨f, hf⟩ := exists_mem_of_iSup_eq_top hcover p
  refine ⟨W f, hf, ?_⟩
  have haff : IsAffine (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)).toScheme :=
    AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 (f : A) f.2 hd
  rw [← Scheme.Hom.resLE_comp_ι (toProj 𝒜 φ) (hW f).ge,
    ← Scheme.Hom.resLE_comp_ι (toProj 𝒜 φ') (hW' f).ge]
  refine congrArg (· ≫ _) (AlgebraicGeometry.ext_of_isAffine ?_)
  simp only [Scheme.Hom.resLE_app_top, happ f]

/-- Two morphisms `φ, φ' : Y ⟶ U_d` that have the same preimage `W f` of each standard open
`D₊(f)` with `f ∈ S_d`, and whose induced ring maps `Γ(X, D₊(f)) ⟶ Γ(Y, W f)` agree on the
elements `a/f^n`, are equal. -/
theorem eq_of_appLE_eq_on_away (hd : 0 < d) {φ φ' : Y ⟶ (degreeOpen 𝒜 d).toScheme}
    {W : 𝒜 d → Y.Opens}
    (hW : ∀ f : 𝒜 d, toProj 𝒜 φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) = W f)
    (hW' : ∀ f : 𝒜 d, toProj 𝒜 φ' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) = W f)
    (happ : ∀ (f : 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)),
      (toProj 𝒜 φ).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) (W f) (hW f).ge
          (AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n a ha)) =
        (toProj 𝒜 φ').appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) (W f) (hW' f).ge
          (AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n a ha))) :
    φ = φ' := by
  refine eq_of_appLE_eq 𝒜 hd hW hW' fun f ↦ ?_
  ext z
  obtain ⟨n, a, ha, hmk⟩ := Away.mk_surjective 𝒜 f.2
    ((AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).inv z)
  have hz : AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n a ha) = z := by
    rw [← AlgebraicGeometry.Proj.basicOpenIsoAway_hom 𝒜 (f : A) f.2 hd, hmk]
    exact ConcreteCategory.congr_hom
      (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).inv_hom_id z
  exact hz ▸ happ f n a ha

/-- Two morphisms `φ, φ' : Y ⟶ U_d` with the same preimage `W f` of each standard open `D₊(f)`,
`f ∈ S_d`, are equal if there are invertible modules `M n`, global sections `sPow f n` of `M n`
that do not vanish on `W f`, and sections `psi f n a ha` of `M n` over `W f` such that
`psi f n a ha = φ^♯(a/f^n) · (sPow f n)|_{W f}` for `φ` and for `φ'`. -/
theorem eq_of_smul_appLE_eq (hd : 0 < d) {φ φ' : Y ⟶ (degreeOpen 𝒜 d).toScheme}
    {W : 𝒜 d → Y.Opens}
    (hW : ∀ f : 𝒜 d, toProj 𝒜 φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) = W f)
    (hW' : ∀ f : 𝒜 d, toProj 𝒜 φ' ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) = W f)
    (M : ℕ → Y.Modules) [∀ n, Stacks.Ample.IsInvertibleModule Y (M n)]
    (sPow : ∀ (_ : 𝒜 d) (n : ℕ), Γ(M n, ⊤))
    (hsPow : ∀ (f : 𝒜 d) (n : ℕ),
      W f ≤ Stacks.NonvanishingOpen.nonvanishingOpen Y (M n) (sPow f n))
    (psi : ∀ (f : 𝒜 d) (n : ℕ) (a : A), a ∈ 𝒜 (n • d) → Γ(M n, W f))
    (hpsi : ∀ (f : 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)), psi f n a ha =
      (toProj 𝒜 φ).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) (W f) (hW f).ge
          (AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n a ha)) •
        (M n).presheaf.map (homOfLE (le_top : W f ≤ ⊤)).op (sPow f n))
    (hpsi' : ∀ (f : 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)), psi f n a ha =
      (toProj 𝒜 φ').appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) (W f) (hW' f).ge
          (AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n a ha)) •
        (M n).presheaf.map (homOfLE (le_top : W f ≤ ⊤)).op (sPow f n)) :
    φ = φ' :=
  eq_of_appLE_eq_on_away 𝒜 hd hW hW' fun f n a ha ↦
    eq_of_smul_restrict_eq (M n) (sPow f n) (hsPow f n) (hpsi f n a ha) (hpsi' f n a ha)

end Morphism

/-! ### The pair is unique -/

section Pair

open Stacks.AlgebraicGeometry.MorphismsIntoProj

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : Scheme.{u}} {d : ℕ}

/-- A pair consisting of a morphism `φ : Y ⟶ U_d` and an isomorphism `φ⁎𝒪_X(d) ≅ L`. -/
abbrev Pair (L : Y.Modules) (d : ℕ) : Type _ :=
  Σ φ : Y ⟶ (degreeOpen 𝒜 d).toScheme, pullbackTwist 𝒜 φ (d : ℤ) ≅ L

/-- Two pairs `(φ, α)` and `(φ', α')` are equal as soon as

* the preimages of each `D₊(f)`, `f ∈ S_d`, under `φ` and under `φ'` are one and the same open
  `W f`;
* `φ` and `φ'` induce the same ring map on the fractions `a/f^n`;
* the nonvanishing opens of global sections `t f` of `L`, `f ∈ S_d`, cover `Y`;
* `α` and `α'` both carry chosen sections `m f` of `φ⁎𝒪_X(d)` to `t f`. -/
theorem pair_eq (hd : 0 < d) {L : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L]
    (p q : Pair 𝒜 L d) {W : 𝒜 d → Y.Opens}
    (hW : ∀ f : 𝒜 d, toProj 𝒜 p.1 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) = W f)
    (hW' : ∀ f : 𝒜 d, toProj 𝒜 q.1 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) = W f)
    (happ : ∀ (f : 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)),
      (toProj 𝒜 p.1).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) (W f) (hW f).ge
          (AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n a ha)) =
        (toProj 𝒜 q.1).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) (W f) (hW' f).ge
          (AlgebraicGeometry.Proj.awayToSection 𝒜 (f : A) (Away.mk 𝒜 f.2 n a ha)))
    {t : 𝒜 d → Γ(L, ⊤)}
    (hcover : ⨆ f : 𝒜 d, Stacks.NonvanishingOpen.nonvanishingOpen Y L (t f) = ⊤)
    {m : ∀ ψ : Y ⟶ (degreeOpen 𝒜 d).toScheme, 𝒜 d → Γ(pullbackTwist 𝒜 ψ (d : ℤ), ⊤)}
    (hp : ∀ f : 𝒜 d, p.2.hom.app ⊤ (m p.1 f) = t f)
    (hq : ∀ f : 𝒜 d, q.2.hom.app ⊤ (m q.1 f) = t f) : p = q := by
  obtain ⟨φ, α⟩ := p
  obtain ⟨φ', α'⟩ := q
  obtain rfl := eq_of_appLE_eq_on_away 𝒜 hd hW hW' happ
  exact congrArg _ (iso_eq_of_app_eq hcover α α' hp hq)

end Pair

end Stacks.AlgebraicGeometry.ProjSectionsUnique

end
