module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver
public import StacksFrontier.CategoryTheory.Sites.Pretopology.CombinatorialEquivalence
public import StacksCore.Tactic.StacksAttribute

/-!
# Coverings of a big étale site

A big étale site admits only set-many covering families, chosen with a bound on their index
types. This file shows that nothing is lost: every covering family one actually meets is
accounted for by one of the chosen families.

Three cases, in increasing strength. An arbitrary étale covering family of an object of the
site, formed in the ambient category of schemes, is *refined* by a chosen family. A standard
étale covering — a finite affine one — and a Zariski covering are, more strongly,
*tautologically equivalent* to a chosen family, so they agree with it up to isomorphisms of
the source schemes.

## Main results

* `AlgebraicGeometry.BigEtaleSite.exists_covering_refining_etale_cover` — an internal
  refinement of an arbitrary ambient étale covering family.
* `AlgebraicGeometry.BigEtaleSite.exists_isCovering_tautologicallyEquivalent_affineCover` —
  a standard étale covering is tautologically equivalent to a chosen family.
* `AlgebraicGeometry.BigEtaleSite.exists_isCovering_tautologicallyEquivalent_openCover` —
  a Zariski covering is tautologically equivalent to a chosen family.

## Implementation notes

A family of morphisms over a fixed object is a `CategoryTheory.PreZeroHypercover`. The given
family has sources in the ambient category of schemes, whereas a chosen family has sources in
the site's cutoff category; the latter is therefore mapped along the site's inclusion before
the two are compared. A refinement is a morphism of pre-zero-hypercovers.

For the refinement statement the given family is first replaced by one indexed by affine opens:
each source is covered by affine opens mapping into an affine open of the target, and such an
affine open is small enough to lie in the cutoff category because it is of finite type and
quasi-compact over an affine open of the target. The resulting family is an étale covering, so
the site's representative exists, and the refinement morphism is the composite of the
representative's comparison with the inclusion of affine opens.

In the two tautological-equivalence statements the given family is already small enough — the
sources of a Zariski covering are open subschemes of the target, and those of a standard étale
covering are affine and of finite type over it — so the family transfers into the cutoff
category directly and only its combinatorial representative has to be found.

## References

* [Stacks Project, Tag 03WW](https://stacks.math.columbia.edu/tag/03WW)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.BigEtaleSite

private lemma affineOpen_etale_size_lt {X Y : AlgebraicGeometry.Scheme.{u}} {κ : Cardinal.{u}}
    (hY : Y.size < κ) (f : X ⟶ Y) (hf : Etale f)
    (V : Y.affineOpens) (U : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) : U.1.toScheme.size < κ := by
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine V.1.toScheme := V.2
  let q : U.1.toScheme ⟶ V.1.toScheme := f.resLE V.1 U.1 hUV
  have : Etale q := Etale.of_comp q V.1.ι
  have : IsAffineHom q := inferInstance
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact q
    (Scheme.size_lt_of_isOpenImmersion V.1.ι hY)

/-- **Stacks Project, Tag 03WW.** Every étale covering family of an object of a big étale
site, formed in the ambient category of schemes, is refined by a covering family internal to
the site. -/
@[stacks 03WW "etale_refinement"]
public theorem exists_covering_refining_etale_cover
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {T : B.Scheme}
    (𝒰 : PreZeroHypercover.{u + 1} (B.inclusion.obj T))
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.etalePrecoverage (B.inclusion.obj T)) :
    ∃ 𝒱 : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, 𝒱⟩ ∧ Nonempty ((𝒱.map B.inclusion).Hom 𝒰) := by
  classical
  have hcover : (∀ x, ∃ i, x ∈ Set.range (𝒰.f i)) ∧ ∀ i, Etale (𝒰.f i) :=
    (Scheme.presieve₀_mem_precoverage_iff 𝒰).mp
      (by simpa only [Scheme.etalePrecoverage] using h𝒰)
  let I : Type (u + 1) :=
    Σ i : 𝒰.I₀, Σ V : T.1.affineOpens,
      {U : (𝒰.X i).affineOpens // U.1 ≤ (𝒰.f i) ⁻¹ᵁ V.1}
  let 𝒱 : PreZeroHypercover.{u + 1} T := {
    I₀ := I
    X a := B.obj (a.2.2.1.1.toScheme)
      (affineOpen_etale_size_lt T.2 (𝒰.f a.1) (hcover.2 a.1)
        a.2.1 a.2.2.1 a.2.2.2)
    f a := ⟨a.2.2.1.1.ι ≫ 𝒰.f a.1⟩
  }
  have h𝒱cover :
      (∀ x, ∃ a : I, x ∈ Set.range ((𝒱.map B.inclusion).f a)) ∧
        ∀ a, Etale ((𝒱.map B.inclusion).f a) := by
    refine ⟨fun x => ?_, fun a => ?_⟩
    · obtain ⟨i, y, hy⟩ := hcover.1 x
      obtain ⟨V, hV, hxV, -⟩ :=
        exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
      have hyV : y ∈ (𝒰.f i) ⁻¹ᵁ V := show 𝒰.f i y ∈ V from hy ▸ hxV
      obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset hyV
      exact ⟨⟨i, ⟨V, hV⟩, ⟨U, hU⟩, hUV⟩, ⟨y, hyU⟩, hy⟩
    · dsimp [𝒱, PreZeroHypercover.map]
      have : Etale (𝒰.f a.1) := hcover.2 a.1
      infer_instance
  let W : Covering B.Scheme := ⟨T, 𝒱⟩
  have hW : AlgebraicGeometry.IsEtaleCovering W :=
    (Scheme.presieve₀_mem_precoverage_iff (𝒱.map B.inclusion)).mpr h𝒱cover
  obtain ⟨W', hW', htarget, hcomb⟩ := B.exists_covering_rep W hW
  cases htarget
  refine ⟨W'.2, hW', ?_⟩
  obtain ⟨β, hX, hf⟩ := hcomb.2
  let χ : (𝒱.map B.inclusion).Hom 𝒰 := {
    s₀ := fun a => a.1
    h₀ := fun a => a.2.2.1.1.ι
    w₀ := fun _ => rfl
  }
  let θ : (W'.2.map B.inclusion).Hom (𝒱.map B.inclusion) := {
    s₀ := β
    h₀ := fun j => B.inclusion.map (eqToHom (hX j))
    w₀ j := by
      change B.inclusion.map (eqToHom (hX j)) ≫
          B.inclusion.map (𝒱.f (β j)) = B.inclusion.map (W'.2.f j)
      rw [← Functor.map_comp, hf j]
  }
  exact ⟨θ.comp χ⟩

private lemma combinatoriallyEquivalent_map_inclusion (B : AlgebraicGeometry.BigEtaleSite.{u})
    {T : B.Scheme} {E F : PreZeroHypercover.{u + 1} T}
    (h : PreZeroHypercover.CombinatoriallyEquivalent E F) :
    PreZeroHypercover.CombinatoriallyEquivalent (E.map B.inclusion) (F.map B.inclusion) := by
  obtain ⟨⟨α, hX, hf⟩, ⟨β, hY, hg⟩⟩ := h
  constructor
  · exact ⟨α, fun i => congrArg B.inclusion.obj (hX i), fun i => by
      simpa [PreZeroHypercover.map] using congrArg B.inclusion.map (hf i)⟩
  · exact ⟨β, fun j => congrArg B.inclusion.obj (hY j), fun j => by
      simpa [PreZeroHypercover.map] using congrArg B.inclusion.map (hg j)⟩

/-- If a family `W` over `T` is an étale covering and is tautologically equivalent to `U` after
mapping to schemes, then `U` is tautologically equivalent to a covering of the site. -/
private theorem exists_isCovering_tautologicallyEquivalent_of_equivalent
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {T : B.Scheme}
    (U : PreZeroHypercover.{u + 1} (B.inclusion.obj T)) (W : PreZeroHypercover.{u + 1} T)
    (hW : AlgebraicGeometry.IsEtaleCovering (⟨T, W⟩ : Covering B.Scheme))
    (hU : PreZeroHypercover.TautologicallyEquivalent U (W.map B.inclusion)) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, V⟩ ∧ PreZeroHypercover.TautologicallyEquivalent U (V.map B.inclusion) := by
  obtain ⟨W', hW', htarget, hcomb⟩ := B.exists_covering_rep ⟨T, W⟩ hW
  cases htarget
  exact ⟨W'.2, hW', PreZeroHypercover.tautologicallyEquivalent_trans U _ _ hU
    (PreZeroHypercover.tautologicallyEquivalent_of_combinatoriallyEquivalent _ _
      (combinatoriallyEquivalent_map_inclusion B hcomb))⟩

/-- **Stacks Project, Tag 03WW.** A standard étale covering of an object of a big étale
site is tautologically equivalent to a covering belonging to that site. -/
@[stacks 03WW "standard_etale_equivalence"]
public theorem exists_isCovering_tautologicallyEquivalent_affineCover
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (T : B.Scheme)
    [IsAffine (B.inclusion.obj T)]
    (U : (B.inclusion.obj T).AffineCover.{u + 1} @Etale) [Finite U.I₀] :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, V⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent U.cover.toPreZeroHypercover
          (V.map B.inclusion) := by
  have hsize : ∀ i, (U.cover.X i).size < B.cutoff := by
    intro i
    have : IsAffine (U.cover.X i) := inferInstanceAs (IsAffine (Spec (U.X i)))
    have : Etale (U.cover.f i) := U.cover.map_prop i
    exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (U.cover.f i) T.2
  let W : Covering B.Scheme :=
    ⟨T, ⟨U.cover.I₀, fun i => B.obj (U.cover.X i) (hsize i),
      fun i => ⟨U.cover.f i⟩⟩⟩
  have hW : AlgebraicGeometry.IsEtaleCovering W := by
    change U.cover.toPreZeroHypercover.presieve₀ ∈
      Scheme.etalePrecoverage (B.inclusion.obj T)
    simpa only [Scheme.etalePrecoverage] using U.cover.mem₀
  exact exists_isCovering_tautologicallyEquivalent_of_equivalent B U.cover.toPreZeroHypercover
    W.2 hW (PreZeroHypercover.tautologicallyEquivalent_refl _)

/-- **Stacks Project, Tag 03WW.** A Zariski covering of an object of a big étale site is
tautologically equivalent to a covering belonging to that site. -/
@[stacks 03WW "zariski_equivalence"]
public theorem exists_isCovering_tautologicallyEquivalent_openCover
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (T : B.Scheme)
    (U : (B.inclusion.obj T).OpenCover.{u + 1}) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, V⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent U.toPreZeroHypercover
          (V.map B.inclusion) := by
  let W : Covering B.Scheme :=
    ⟨T, ⟨U.I₀, fun i => B.obj (U.X i) (Scheme.size_lt_of_isOpenImmersion (U.f i) T.2),
      fun i => ⟨U.f i⟩⟩⟩
  have hW : AlgebraicGeometry.IsEtaleCovering W := by
    change (W.2.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage (B.inclusion.obj T)
    exact Scheme.precoverage_mono (P := @IsOpenImmersion) (Q := @Etale)
      (fun _ _ _ _ => inferInstance)
      (B.inclusion.obj T) (by simpa [W, PreZeroHypercover.map] using U.mem₀)
  exact exists_isCovering_tautologicallyEquivalent_of_equivalent B U.toPreZeroHypercover W.2 hW
    (by constructor <;> exact ⟨id, fun i => ⟨eqToIso rfl, rfl⟩⟩)

end AlgebraicGeometry.BigEtaleSite
