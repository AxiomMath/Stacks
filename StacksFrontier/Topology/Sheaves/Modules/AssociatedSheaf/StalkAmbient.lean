module

public import StacksFrontier.Algebra.Module.Projective.Determinant.SemilinearBaseChange
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.StalkBaseChange

/-!
# The rank idempotent on the stalks of the ambient ringed space

Let `(W, 𝒪_W)` be a ringed space, `U ⊆ W` an open, `F` a sheaf of `𝒪_W`-modules and `M` a finite
projective `𝒪_W(U)`-module with `F|_U ≅ ℱ_M` on the restricted ringed space `W|_U`. The germ at a
point `x ∈ U`, taken in `𝒪_W`, of `ProjectiveDeterminant.rankIdempotent 𝒪_W(U) M n` is the
rank-`n` idempotent of the stalk of `F` at `x` over the local ring of `W` at `x`.

## Main results

* `Stacks.AssociatedSheaf.smul_of_germ_smul`: **germ-level semilinearity promotes to the whole
  stalk.** For `P` a presheaf of `𝒪`-modules on a space, a pair of maps out of the stalk of `𝒪`
  and the stalk of `P` at a point which is semilinear on germs over every open neighbourhood is
  semilinear on all of the stalk.
* `Stacks.AssociatedSheaf.germ_rankIdempotent_eq_rankIdempotent_stalk_of_restrict`: **the rank
  idempotent matches the stalks of the ambient space.** The germ at a point of `U`, taken in
  `𝒪_W`, of `ProjectiveDeterminant.rankIdempotent 𝒪_W(U) M n` is the rank-`n` idempotent of the
  stalk of `F` at that point over the local ring of `W` there.

## Implementation notes

**Which module structure on the stalk.** Two definitionally equal `Module` instances on the stalk
of a presheaf of modules are in play — Mathlib's, which
`Stacks.AssociatedSheaf.presheafStalkModuleFunctor` and hence `Stacks.AssociatedSheaf.stalkModule`
are built from, and the repository's `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` —
and under the module system they are *not* interchangeable even by a definitional-equality check:
unfolding one into the other has to pass through `CategoryTheory.Limits.getColimitCocone`, whose
definition the module system does not expose, so the check stops there. The proof below therefore
stays on Mathlib's instance throughout on the restricted space, which is the one the statements of
`StalkBaseChange` are written at, and uses Mathlib's `PresheafOfModules.germ_smul` rather than the
repository's `stalkModule_germ_smul`; the ambient stalk is left to instance search, which finds
the repository's. Instance search does **not** find either instance at the restricted space's
spelling of the point, which is why the proof names it with `letI`.

**The open the germ is taken over.** `𝒪_W(U)` appears as
`(W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)`, the global sections of the restricted space,
which is `𝒪_W` evaluated at the image of `⊤`; so the germ is taken over
`(TopCat.Presheaf.imF U).obj ⊤` rather than over `U`. The two opens are equal, but not
syntactically, and the type of `M` depends on the first, so the statement is given there.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH), clause (3).
* [Stacks Project, Tag 08BL](https://stacks.math.columbia.edu/tag/08BL)
* [Stacks Project, Section 0FJ9](https://stacks.math.columbia.edu/tag/0FJ9)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AssociatedSheaf

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

/-! ### Germ-level semilinearity promotes to the whole stalk -/

section Generic

variable {Y : TopCat.{u}} {O : Y.Presheaf CommRingCat.{u}}
  (P : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (y : Y)
  {S : Type u} [CommRing S] {N : Type u} [AddCommGroup N] [Module S N]
  (φ : ToType (O.stalk y) → S)
  (Φ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P.presheaf y) → N)

/-- **A pair of maps out of the stalks which is semilinear on germs is semilinear.** If
`Φ (r • m) = φ r • Φ m` for the germs `r` and `m` of sections over every open neighbourhood of `y`,
then it holds for all `r` in the stalk of `O` and `m` in the stalk of `P` at `y`. Neither `φ` nor
`Φ` is assumed to be a homomorphism. -/
theorem smul_of_germ_smul
    (h : ∀ (V : Opens Y) (hV : y ∈ V) (r : ToType (O.obj (op V))) (m : ToType (P.obj (op V))),
      Φ (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) P.presheaf V y hV (r • m)) =
        φ (O.germ V y hV r) •
          Φ (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) P.presheaf V y hV m))
    (r : ToType (O.stalk y))
    (m : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P.presheaf y)) :
    Φ (r • m) = φ r • Φ m := by
  obtain ⟨V₁, h₁, r₀, hr₀⟩ := TopCat.Presheaf.exists_germ_eq O r
  obtain ⟨V₂, h₂, m₀, hm₀⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) P.presheaf m
  have hV : y ∈ V₁ ⊓ V₂ := ⟨h₁, h₂⟩
  set r' := (O.map (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op) r₀ with hr'
  set m' := (P.map (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op) m₀ with hm'
  have hr : O.germ (V₁ ⊓ V₂) y hV r' = r :=
    (TopCat.Presheaf.germ_res_apply O
      (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)) y hV r₀).trans hr₀
  have hm : TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) P.presheaf (V₁ ⊓ V₂) y hV m' = m :=
    (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) P.presheaf
      (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)) y hV m₀).trans hm₀
  rw [← hr, ← hm, ← PresheafOfModules.germ_smul P y (V₁ ⊓ V₂) hV r' m']
  exact h (V₁ ⊓ V₂) hV r' m'

end Generic

/-! ### The rank idempotent on the stalks of the ambient space -/

section Restrict

variable {W : RingedSpace.{u, u}} (U : Opens W.carrier)
  (F : SheafOfModules.{u} (structureSheafRing W)) {x : W.carrier} (hU : x ∈ U)

/-- **The rank idempotent matches the stalks of the ambient ringed space.** For `M` a finite
projective `𝒪_W(U)`-module with `F|_U ≅ ℱ_M` on `W|_U`, the germ at a point of `U`, taken on `W`,
of the idempotent cutting out the rank-`n` stratum of `M` is the idempotent cutting out the
rank-`n` stratum of the stalk of `F` there, over the local ring of `W`, the stalk being assumed
finite and projective. -/
theorem germ_rankIdempotent_eq_rankIdempotent_stalk_of_restrict
    (M : ModuleCat.{u} ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)))
    [Module.Finite ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) M]
    [Module.Projective ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) M]
    (e : restrictOver U F ≅ associatedSheaf (W.restrict U.isOpenEmbedding)
      (RingHom.id ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))) M)
    (n : ℕ)
    (hfin : Module.Finite (ToType (W.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (valOf F).presheaf x)))
    (hproj : Module.Projective (ToType (W.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (valOf F).presheaf x))) :
    letI := hfin
    letI := hproj
    W.presheaf.germ ((TopCat.Presheaf.imF U).obj ⊤) x
        ⟨(⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier), trivial, rfl⟩
        (ProjectiveDeterminant.rankIdempotent
          (R := (W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) (M := M) n) =
      ProjectiveDeterminant.rankIdempotent (R := ToType (W.presheaf.stalk x))
        (M := ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (valOf F).presheaf x))
        n := by
  let := hfin
  let := hproj
  let instR : Module
      (ToType ((W.restrict U.isOpenEmbedding).presheaf.stalk
        (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (restrictValOf U F).presheaf
        (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier))) :=
    (stalkModule (W.restrict U.isOpenEmbedding) (restrictOver U F)
      (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)).isModule
  let hfinR : Module.Finite
      (ToType ((W.restrict U.isOpenEmbedding).presheaf.stalk
        (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (restrictValOf U F).presheaf
        (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier))) :=
    moduleFinite_stalkOfIso (W.restrict U.isOpenEmbedding)
      (RingHom.id ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))) M (restrictOver U F)
      (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) e
  let hprojR : Module.Projective
      (ToType ((W.restrict U.isOpenEmbedding).presheaf.stalk
        (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (restrictValOf U F).presheaf
        (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier))) :=
    moduleProjective_stalkOfIso (W.restrict U.isOpenEmbedding)
      (RingHom.id ((W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))) M (restrictOver U F)
      (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier) e
  have hsl := smul_of_germ_smul (restrictValOf U F)
    (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)
    (restrictStalkCommRingEquiv U hU) (restrictStalkAddEquiv U F hU)
    (fun V hV r₀ m₀ => restrictStalkAddEquiv_germ_smul U F hU V hV r₀ m₀)
  have hrank : restrictStalkCommRingEquiv U hU
        (ProjectiveDeterminant.rankIdempotent
          (R := ToType ((W.restrict U.isOpenEmbedding).presheaf.stalk
            (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier)))
          (M := ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
            (restrictValOf U F).presheaf
            (⟨x, hU⟩ : (W.restrict U.isOpenEmbedding).carrier))) n) =
      ProjectiveDeterminant.rankIdempotent (R := ToType (W.presheaf.stalk x))
        (M := ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (valOf F).presheaf x)) n :=
    ProjectiveDeterminant.rankIdempotent_eq_of_semilinearEquiv
      (restrictStalkCommRingEquiv U hU) (restrictStalkAddEquiv U F hU) hsl n
  have hrestrict := germ_rankIdempotent_eq_rankIdempotent_restrictStalk U F hU M e n
  have hgerm := restrictStalkCommRingEquiv_germ U hU ⊤ trivial
    (ProjectiveDeterminant.rankIdempotent
      (R := (W.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) (M := M) n)
  exact hgerm.symm.trans
    ((congrArg (restrictStalkCommRingEquiv U hU) hrestrict).trans hrank)

end Restrict

end Stacks.AssociatedSheaf

end
