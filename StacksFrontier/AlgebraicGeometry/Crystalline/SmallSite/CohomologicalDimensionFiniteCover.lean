module

public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.Algebra.Homology.RightDerivedBiprod
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CohomologicalDimensionLocalToGlobal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RelativeMayerVietoris

/-!
# Vanishing of crystalline cohomology from a finite open covering

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], an abelian sheaf
`F` on `Cris(X/S)`, an integer `d ≥ 0` and a finite family `U₀, …, U_{n-1}` of opens of `X`
with `X = U₀ ∪ ⋯ ∪ U_{n-1}`. Suppose that over every nonempty finite intersection
`V = U_{i₁} ∩ ⋯ ∩ U_{i_k}` the cohomology of `F` on the crystalline site of `V` vanishes in every
degree `> d`. Then `H^j(Cris(X/S), F) = 0` for every `j ≥ d + n`, that is `j > d + n - 1`.

No dimension hypothesis is made on `X`; the bound comes from the number of opens alone. This is
the form needed when `X` lives over a base whose Krull dimension may be infinite, so that the
Grothendieck vanishing route of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CohomologicalDimensionLocalToGlobal.lean` is
not available. When `X` is separated and the `U_i` are affine, the intersections are affine,
which is what makes the hypothesis checkable in practice; neither is needed for the statement.

## The proof

For an open `V` of `X` write `Γ_V = Γ(V, u_{X/S, *} -)`, the functor
`...SmallSite.zariskiDirectImageSections`. Its right derived functors are the cohomology of the
crystalline site of `V` ([Stacks, Tag 07KL],
`...SmallSite.isZero_rightDerived_zariskiDirectImageSections_of_isZero`), and `Γ_X` is
`Γ(Cris(X/S), -)` (`...SmallSite.zariskiDirectImageSectionsTopIso`).

For opens `A`, `B` of `X`, the sequence `0 ⟶ Γ_{A ∪ B} ⟶ Γ_A ⊕ Γ_B ⟶ Γ_{A ∩ B} ⟶ 0` is short
exact at every injective sheaf `I`: `u_{X/S, *}` preserves injectives, and the sections of an
injective abelian sheaf on `X_Zar` over the Mayer--Vietoris square of `A` and `B` form a short
exact sequence (`Stacks.EtaleCohomology.RelativeMayerVietoris.sectionShortComplex_shortExact`).
Its long exact sequence, `CategoryTheory.longExact_rightDerived_of_shortExact_on_injectives`,
gives `R^{q + 1} Γ_{A ∪ B} F = 0` as soon as `R^q Γ_{A ∩ B} F`, `R^{q + 1} Γ_A F` and
`R^{q + 1} Γ_B F` vanish.

Induction on `n`: write `X' = U₀ ∪ ⋯ ∪ U_{n-1}` and add `U_n`. The opens `X'` and
`X' ∩ U_n = ⋃_{i < n} (U_i ∩ U_n)` are unions of `n` opens whose finite intersections are finite
intersections of the `U_i`, and `U_n` is one of them, so the long exact sequence raises the bound
by one. The case `n = 0` is `V = ∅`, over which every sheaf has zero sections.

## Main results

All in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `isZero_rightDerived_zariskiDirectImageSections_sup` — the Mayer--Vietoris step.
* `isZero_rightDerived_zariskiDirectImageSections_iSup` — the bound for `Γ_V`, `V` a union of
  `n` opens.
* `subsingleton_cohomology_of_finiteCover` — **the abelian form**: `H^j(Cris(X/S), F) = 0` for
  `j ≥ d + n`.
* `isZero_cohomologyFunctor_obj_of_finiteCover` — the same for `cohomologyFunctor S j`.
* `isZero_homology_moduleULiftDerivedGlobalSections_of_finiteCover` — **the module form**: for
  a sheaf of `𝒪_{X/S}`-modules, the cohomology of `RΓ(Cris(X/S), F) ∈ D⁺(Mod_A)` vanishes in
  degrees `≥ d + n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### The Mayer--Vietoris square of two opens of `X` -/

/-- **The Mayer--Vietoris square of two opens `A`, `B` of `X`** in the small Zariski site:
`A ∩ B ⟶ A`, `A ∩ B ⟶ B`, `A ⟶ A ∪ B`, `B ⟶ A ∪ B`. -/
def zariskiOpensSquare (A B : S.X.Opens) : Square S.X.Opens where
  X₁ := A ⊓ B
  X₂ := A
  X₃ := B
  X₄ := A ⊔ B
  f₁₂ := homOfLE inf_le_left
  f₁₃ := homOfLE inf_le_right
  f₂₄ := homOfLE le_sup_left
  f₃₄ := homOfLE le_sup_right
  fac := Subsingleton.elim _ _

/-- The Mayer--Vietoris square of two opens is cartesian: in the lattice of opens the pullback
of `A ⟶ A ∪ B` and `B ⟶ A ∪ B` is the intersection. -/
theorem isPullback_zariskiOpensSquare (A B : S.X.Opens) :
    (zariskiOpensSquare S A B).IsPullback :=
  ⟨⟨Subsingleton.elim _ _⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => homOfLE (le_inf (leOfHom s.fst) (leOfHom s.snd)))
    (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ _ => Subsingleton.elim _ _)⟩⟩

/-- The two inclusions `A ⟶ A ∪ B` and `B ⟶ A ∪ B` generate a covering sieve of `A ∪ B`. -/
theorem ofTwoArrows_zariskiOpensSquare_mem (A B : S.X.Opens) :
    Sieve.ofTwoArrows (zariskiOpensSquare S A B).f₂₄ (zariskiOpensSquare S A B).f₃₄ ∈
      opensTopology S (zariskiOpensSquare S A B).X₄ := by
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  rcases (Opens.mem_sup.1 hx) with hx | hx
  · exact ⟨A, (zariskiOpensSquare S A B).f₂₄,
      Sieve.ofArrows_mk _ _ WalkingPair.left, hx⟩
  · exact ⟨B, (zariskiOpensSquare S A B).f₃₄,
      Sieve.ofArrows_mk _ _ WalkingPair.right, hx⟩

/-- The inclusion `A ∩ B ⟶ A` of opens is a monomorphism. -/
instance mono_zariskiOpensSquare_f₁₂ (A B : S.X.Opens) : Mono (zariskiOpensSquare S A B).f₁₂ :=
  ⟨fun _ _ _ => Subsingleton.elim _ _⟩

/-- The inclusion `A ⟶ A ∪ B` of opens is a monomorphism. -/
instance mono_zariskiOpensSquare_f₂₄ (A B : S.X.Opens) : Mono (zariskiOpensSquare S A B).f₂₄ :=
  ⟨fun _ _ _ => Subsingleton.elim _ _⟩

/-- The inclusion `B ⟶ A ∪ B` of opens is a monomorphism. -/
instance mono_zariskiOpensSquare_f₃₄ (A B : S.X.Opens) : Mono (zariskiOpensSquare S A B).f₃₄ :=
  ⟨fun _ _ _ => Subsingleton.elim _ _⟩

/-! ### Restriction maps between the section functors -/

/-- **Restriction `Γ(V, u_{X/S, *} -) ⟶ Γ(W, u_{X/S, *} -)` along `W ≤ V`**, as a natural
transformation of functors of the abelian sheaf. -/
def zariskiDirectImageSectionsRes {W V : S.X.Opens} (h : W ≤ V) :
    zariskiDirectImageSections S V ⟶ zariskiDirectImageSections S W :=
  Functor.whiskerLeft _ ((evaluation (S.X.Opens)ᵒᵖ AddCommGrpCat.{u + 1}).map (homOfLE h).op)

/-- The component of the restriction map at a sheaf is the restriction map of its direct
image. -/
theorem zariskiDirectImageSectionsRes_app {W V : S.X.Opens} (h : W ≤ V)
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (zariskiDirectImageSectionsRes S h).app F =
      ((zariskiDirectImage S).obj F).obj.map (homOfLE h).op :=
  rfl

/-- Restriction maps compose. -/
theorem zariskiDirectImageSectionsRes_comp {W V V' : S.X.Opens} (h : W ≤ V) (h' : V ≤ V') :
    zariskiDirectImageSectionsRes S h' ≫ zariskiDirectImageSectionsRes S h =
      zariskiDirectImageSectionsRes S (h.trans h') := by
  refine NatTrans.ext (funext fun F => ?_)
  rw [NatTrans.comp_app, zariskiDirectImageSectionsRes_app, zariskiDirectImageSectionsRes_app,
    zariskiDirectImageSectionsRes_app]
  exact (Functor.map_comp _ _ _).symm.trans (congrArg
    (fun k => ((zariskiDirectImage S).obj F).obj.map k.op)
    (Subsingleton.elim (homOfLE h ≫ homOfLE h') (homOfLE (h.trans h'))))

/-! ### The Mayer--Vietoris short complex of section functors -/

section Biprod

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

variable (A B : S.X.Opens)

/-- The first map of the Mayer--Vietoris short complex, `Γ_{A ∪ B} ⟶ Γ_A ⊞ Γ_B`. -/
def zariskiMayerVietorisFst :
    zariskiDirectImageSections S (A ⊔ B) ⟶
      zariskiDirectImageSections S A ⊞ zariskiDirectImageSections S B :=
  biprod.lift (zariskiDirectImageSectionsRes S le_sup_left)
    (zariskiDirectImageSectionsRes S le_sup_right)

/-- The second map of the Mayer--Vietoris short complex, `Γ_A ⊞ Γ_B ⟶ Γ_{A ∩ B}`, the difference
of the two restrictions. -/
def zariskiMayerVietorisSnd :
    zariskiDirectImageSections S A ⊞ zariskiDirectImageSections S B ⟶
      zariskiDirectImageSections S (A ⊓ B) :=
  biprod.desc (zariskiDirectImageSectionsRes S inf_le_left)
    (-zariskiDirectImageSectionsRes S inf_le_right)

/-- The two maps of the Mayer--Vietoris short complex compose to zero. -/
theorem zariskiMayerVietorisFst_comp_snd :
    zariskiMayerVietorisFst S A B ≫ zariskiMayerVietorisSnd S A B = 0 := by
  dsimp only [zariskiMayerVietorisFst, zariskiMayerVietorisSnd]
  rw [biprod.lift_desc, Preadditive.comp_neg, zariskiDirectImageSectionsRes_comp,
    zariskiDirectImageSectionsRes_comp, add_neg_cancel]

/-- **The Mayer--Vietoris short complex `Γ_{A ∪ B} ⟶ Γ_A ⊞ Γ_B ⟶ Γ_{A ∩ B}`** of section
functors on `Ab(Cris(X/S))`. -/
abbrev zariskiMayerVietorisComplex :
    ShortComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (zariskiMayerVietorisFst S A B) (zariskiMayerVietorisSnd S A B)
    (zariskiMayerVietorisFst_comp_snd S A B)

/-- Evaluated at a sheaf `I`, the Mayer--Vietoris short complex of section functors is the
Mayer--Vietoris short complex of sections of `u_{X/S, *} I` over the square of `A` and `B`. -/
def zariskiMayerVietorisComplexIso (I : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    (zariskiMayerVietorisComplex S A B).map ((evaluation _ _).obj I) ≅
      Stacks.EtaleCohomology.RelativeMayerVietoris.sectionShortComplex (opensTopology S)
        (zariskiOpensSquare S A B) ((zariskiDirectImage S).obj I) := by
  let E : (Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}) ⥤
      AddCommGrpCat.{u + 1} := (evaluation _ _).obj I
  letI : PreservesBinaryBiproducts E := preservesBinaryBiproducts_of_preservesBinaryProducts E
  refine ShortComplex.isoMk (Iso.refl _) (E.mapBiprod _ _) (Iso.refl _) ?_ ?_
  · exact (Category.id_comp _).trans
      (biprod.map_lift_mapBiprod E (zariskiDirectImageSections S A)
        (zariskiDirectImageSections S B) (zariskiDirectImageSectionsRes S le_sup_left)
        (zariskiDirectImageSectionsRes S le_sup_right)).symm
  · have hneg : E.map (-zariskiDirectImageSectionsRes S (inf_le_right : A ⊓ B ≤ B)) =
        -E.map (zariskiDirectImageSectionsRes S (inf_le_right : A ⊓ B ≤ B)) := E.map_neg
    exact (congrArg (fun k => (E.mapBiprod (zariskiDirectImageSections S A)
        (zariskiDirectImageSections S B)).hom ≫
          biprod.desc (E.map (zariskiDirectImageSectionsRes S (inf_le_left : A ⊓ B ≤ A))) k)
        hneg.symm).trans
      ((biprod.mapBiprod_hom_desc E (zariskiDirectImageSections S A)
        (zariskiDirectImageSections S B)
        (zariskiDirectImageSectionsRes S (inf_le_left : A ⊓ B ≤ A))
        (-zariskiDirectImageSectionsRes S (inf_le_right : A ⊓ B ≤ B))).trans
        (Category.comp_id _).symm)

/-- **The Mayer--Vietoris short complex of section functors is short exact at every injective
abelian sheaf.** `u_{X/S, *}` carries an injective sheaf to an injective sheaf on `X_Zar`, and
the sections of an injective abelian sheaf over the Mayer--Vietoris square of two opens are short
exact. -/
theorem shortExact_zariskiMayerVietorisComplex
    (I : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hI : Injective I) :
    (NatTrans.appShortComplex (zariskiMayerVietorisFst S A B) (zariskiMayerVietorisSnd S A B)
      (zariskiMayerVietorisFst_comp_snd S A B) I).ShortExact := by
  have := hI
  exact ShortComplex.shortExact_of_iso (zariskiMayerVietorisComplexIso S A B I).symm
    (Stacks.EtaleCohomology.RelativeMayerVietoris.sectionShortComplex_shortExact
      (opensTopology S) (zariskiOpensSquare S A B) (isPullback_zariskiOpensSquare S A B)
      (ofTwoArrows_zariskiOpensSquare_mem S A B) ((zariskiDirectImage S).obj I))

/-- A biproduct of two functors is zero at an object where both functors are zero. -/
theorem isZero_biprod_obj_of_isZero {C D : Type*} [Category* C] [Category* D] [Preadditive D]
    (Φ Ψ : C ⥤ D) [HasBinaryBiproduct Φ Ψ] (X : C) (hΦ : IsZero (Φ.obj X))
    (hΨ : IsZero (Ψ.obj X)) : IsZero ((Φ ⊞ Ψ).obj X) := by
  rw [IsZero.iff_id_eq_zero]
  have h := congrArg (fun t : Φ ⊞ Ψ ⟶ Φ ⊞ Ψ => t.app X) (biprod.total (X := Φ) (Y := Ψ))
  simp only [NatTrans.app_add, NatTrans.comp_app, NatTrans.id_app] at h
  rw [← h, hΦ.eq_of_tgt ((biprod.fst : Φ ⊞ Ψ ⟶ Φ).app X) 0,
    hΨ.eq_of_tgt ((biprod.snd : Φ ⊞ Ψ ⟶ Ψ).app X) 0, zero_comp, zero_comp, add_zero]

/-- **The Mayer--Vietoris step.** For opens `A`, `B` of `X` and an abelian sheaf `F` on
`Cris(X/S)`, `R^{q + 1} Γ_{A ∪ B} F = 0` as soon as `R^q Γ_{A ∩ B} F = 0`,
`R^{q + 1} Γ_A F = 0` and `R^{q + 1} Γ_B F = 0`: the long exact sequence of the Mayer--Vietoris
short complex contains `R^q Γ_{A ∩ B} F ⟶ R^{q + 1} Γ_{A ∪ B} F ⟶ R^{q + 1} Γ_A F ⊕
R^{q + 1} Γ_B F`. -/
theorem isZero_rightDerived_zariskiDirectImageSections_sup
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (q : ℕ)
    (hAB : IsZero (((zariskiDirectImageSections S (A ⊓ B)).rightDerived q).obj F))
    (hA : IsZero (((zariskiDirectImageSections S A).rightDerived (q + 1)).obj F))
    (hB : IsZero (((zariskiDirectImageSections S B).rightDerived (q + 1)).obj F)) :
    IsZero (((zariskiDirectImageSections S (A ⊔ B)).rightDerived (q + 1)).obj F) := by
  obtain ⟨delta, -, hex⟩ := longExact_rightDerived_of_shortExact_on_injectives
    (zariskiMayerVietorisFst S A B) (zariskiMayerVietorisSnd S A B)
    (zariskiMayerVietorisFst_comp_snd S A B) (shortExact_zariskiMayerVietorisComplex S A B)
  have hmid : IsZero (((zariskiDirectImageSections S A ⊞ zariskiDirectImageSections S B
      ).rightDerived (q + 1)).obj F) :=
    IsZero.of_iso (isZero_biprod_obj_of_isZero _ _ F hA hB)
      ((Functor.rightDerivedBiprodIso (zariskiDirectImageSections S A)
        (zariskiDirectImageSections S B) (q + 1)).app F)
  exact ((hex q F).exact 2).isZero_of_both_isZero hAB hmid

end Biprod

/-! ### The empty open and the whole space -/

/-- **Over the empty open every right derived functor of `Γ_∅` vanishes**: a sheaf has zero
sections over `∅`, so `Γ_∅` is the zero functor, whose identity is zero, and so is the identity
of each of its right derived functors. -/
theorem isZero_rightDerived_zariskiDirectImageSections_bot
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (p : ℕ) :
    IsZero (((zariskiDirectImageSections S ⊥).rightDerived p).obj F) := by
  have hzero : ∀ G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1},
      IsZero ((zariskiDirectImageSections S ⊥).obj G) := fun G =>
    IsZero.of_iso (isZero_zero _)
      ((TopCat.Sheaf.isTerminalOfEmpty ((zariskiDirectImage S).obj G)).uniqueUpToIso
        (isZero_zero _).isTerminal)
  have hid : 𝟙 (zariskiDirectImageSections S ⊥) = 0 :=
    NatTrans.ext (funext fun G => (hzero G).eq_of_src _ _)
  rw [IsZero.iff_id_eq_zero]
  have h := congrArg (fun t => (NatTrans.rightDerived t p).app F) hid
  simpa only [NatTrans.rightDerived_id, NatTrans.rightDerived_zero, NatTrans.id_app,
    NatTrans.app_zero] using h

/-- **`Γ_X = Γ(Cris(X/S), -)`**: the sections of `u_{X/S, *}` over the whole of `X` are the
global sections of `X_Zar`, `X` being the terminal open, and global sections of `u_{X/S, *}F`
are global sections of `F` (`...SmallSite.zariskiGlobalSectionsDirectImageIso`). -/
def zariskiDirectImageSectionsTopIso :
    zariskiDirectImageSections S ⊤ ≅ globalSections S :=
  Functor.isoWhiskerLeft (zariskiDirectImage S)
      (Sheaf.ΓNatIsoSheafSections (opensTopology S) AddCommGrpCat.{u + 1} isTerminalTop).symm ≪≫
    zariskiGlobalSectionsDirectImageIso S

/-! ### The bound from a finite covering -/

/-- **The Mayer--Vietoris bound for a union of `n` opens.** Let `U₀, …, U_{n-1}` be opens of `X`
and `F` an abelian sheaf on `Cris(X/S)` such that, for every nonempty finite set `s` of indices,
`R^p Γ(⋂_{i ∈ s} U_i, u_{X/S, *} -)(F) = 0` for every `p > d`. Then
`R^p Γ(⋃_i U_i, u_{X/S, *} -)(F) = 0` for every `p ≥ d + n`. -/
theorem isZero_rightDerived_zariskiDirectImageSections_iSup
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (d : ℕ) :
    ∀ (n : ℕ) (U : Fin n → S.X.Opens),
      (∀ s : Finset (Fin n), s.Nonempty → ∀ p : ℕ, d < p →
        IsZero (((zariskiDirectImageSections S (s.inf U)).rightDerived p).obj F)) →
      ∀ p : ℕ, d + n ≤ p →
        IsZero (((zariskiDirectImageSections S (⨆ i, U i)).rightDerived p).obj F) := by
  intro n
  induction n with
  | zero =>
    intro U _ p _
    rw [iSup_of_empty]
    exact isZero_rightDerived_zariskiDirectImageSections_bot S F p
  | succ n ih =>
    intro U hU p hp
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    set A : S.X.Opens := ⨆ i : Fin n, U i.castSucc with hAdef
    set B : S.X.Opens := U (Fin.last n) with hBdef
    have hsup : (⨆ i, U i) = A ⊔ B := by
      refine le_antisymm (iSup_le fun i => ?_)
        (sup_le (iSup_le fun j => le_iSup U j.castSucc) (le_iSup U (Fin.last n)))
      induction i using Fin.lastCases with
      | last => exact le_sup_right
      | cast j => exact le_sup_of_le_left (le_iSup (fun j : Fin n => U j.castSucc) j)
    have hinf : A ⊓ B = ⨆ i : Fin n, (U i.castSucc ⊓ B) := iSup_inf_eq _ _
    have hmap : ∀ s : Finset (Fin n),
        s.inf (fun i => U i.castSucc) = (s.map Fin.castSuccEmb).inf U := fun s => by
      rw [Finset.inf_map]
      rfl
    rw [hsup]
    refine isZero_rightDerived_zariskiDirectImageSections_sup S A B F q ?_ ?_ ?_
    · rw [hinf]
      refine ih (fun i => U i.castSucc ⊓ B) (fun s hs p hp' => ?_) q (by omega)
      have hs' : s.inf (fun i => U i.castSucc ⊓ B) =
          (insert (Fin.last n) (s.map Fin.castSuccEmb)).inf U := by
        rw [Finset.inf_insert, ← hmap, inf_comm]
        exact (Finset.inf_inf ..).trans (by rw [Finset.inf_const hs])
      rw [hs']
      exact hU _ (Finset.insert_nonempty _ _) p hp'
    · refine ih (fun i => U i.castSucc) (fun s hs p hp' => ?_) (q + 1) (by omega)
      rw [hmap]
      exact hU _ hs.map p hp'
    · have h := hU {Fin.last n} (Finset.singleton_nonempty _) (q + 1) (by omega)
      rwa [Finset.inf_singleton] at h

/-- The bound for `Γ_X = Γ(Cris(X/S), -)` when the `n` opens cover `X`: `R^p Γ(Cris(X/S), -)`
vanishes at `F` for `p ≥ d + n`. -/
theorem isZero_rightDerived_globalSections_of_finiteCover
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (d n : ℕ) (U : Fin n → S.X.Opens)
    (hcov : ⨆ i, U i = ⊤)
    (hU : ∀ s : Finset (Fin n), s.Nonempty → ∀ p : ℕ, d < p →
      IsZero (((zariskiDirectImageSections S (s.inf U)).rightDerived p).obj F))
    (p : ℕ) (hp : d + n ≤ p) :
    IsZero (((globalSections S).rightDerived p).obj F) := by
  have h := isZero_rightDerived_zariskiDirectImageSections_iSup S F d n U hU p hp
  rw [hcov] at h
  exact IsZero.of_iso h
    ((Functor.rightDerivedIsoOfNatIso (zariskiDirectImageSectionsTopIso S) p).app F).symm

/-- **Vanishing of crystalline cohomology from a finite open covering, abelian form.** Let
`U₀, …, U_{n-1}` be opens of `X` with `X = ⋃ U_i`, and `F` an abelian sheaf on `Cris(X/S)`.
Suppose that every nonempty finite intersection `V = ⋂_{i ∈ s} U_i` maps into some open `W` of
`S` such that the cohomology of the restriction of `F` to the crystalline site `Cris(V/S|_W)` of
the restricted situation vanishes in every degree `> d`. Then `H^j(Cris(X/S), F) = 0` for every
`j ≥ d + n`, that is for `j > d + n - 1`.

No dimension or finiteness hypothesis is made on `X` or `S`; the open `W` may be `S` itself. -/
theorem subsingleton_cohomology_of_finiteCover
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (d n : ℕ) (U : Fin n → S.X.Opens)
    (hcov : ⨆ i, U i = ⊤)
    (hU : ∀ s : Finset (Fin n), s.Nonempty →
      ∃ (W : S.S.scheme.Opens) (hVW : (⨅ i ∈ s, U i) ≤ sourceToBase S ⁻¹ᵁ W),
        ∀ j : ℕ, d < j → Subsingleton (cohomology (restrict S W (⨅ i ∈ s, U i) hVW)
          ((smallExtendAbelianRestriction S W (⨅ i ∈ s, U i) hVW).obj F) j))
    (j : ℕ) (hj : d + n ≤ j) : Subsingleton (cohomology S F j) := by
  refine (subsingleton_cohomology_iff_isZero_rightDerivedGlobalSections S F j).2
    (isZero_rightDerived_globalSections_of_finiteCover S F d n U hcov (fun s hs p hp => ?_) j hj)
  obtain ⟨W, hVW, hW⟩ := hU s hs
  rw [Finset.inf_eq_iInf]
  exact isZero_rightDerived_zariskiDirectImageSections_of_isZero S W _ hVW p F
    ((subsingleton_cohomology_iff_isZero_rightDerivedGlobalSections _ _ p).1 (hW p hp))

/-- The abelian form read on `cohomologyFunctor S j`: `H^j(Cris(X/S), F)` is a zero object for
`j ≥ d + n`, under the hypotheses of `subsingleton_cohomology_of_finiteCover`. -/
theorem isZero_cohomologyFunctor_obj_of_finiteCover
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (d n : ℕ) (U : Fin n → S.X.Opens)
    (hcov : ⨆ i, U i = ⊤)
    (hU : ∀ s : Finset (Fin n), s.Nonempty →
      ∃ (W : S.S.scheme.Opens) (hVW : (⨅ i ∈ s, U i) ≤ sourceToBase S ⁻¹ᵁ W),
        ∀ j : ℕ, d < j → Subsingleton (cohomology (restrict S W (⨅ i ∈ s, U i) hVW)
          ((smallExtendAbelianRestriction S W (⨅ i ∈ s, U i) hVW).obj F) j))
    (j : ℕ) (hj : d + n ≤ j) : IsZero ((cohomologyFunctor S j).obj F) :=
  have := subsingleton_cohomology_of_finiteCover S F d n U hcov hU j hj
  AddCommGrpCat.isZero_iff_subsingleton.2 this

/-- **Vanishing of crystalline cohomology from a finite open covering, module form.** For a sheaf
`F` of `𝒪_{X/S}`-modules, opens `U₀, …, U_{n-1}` covering `X`, and every nonempty finite
intersection `V = ⋂_{i ∈ s} U_i` mapping into an open `W` of `S` over which the cohomology of the
underlying abelian sheaf of `F` on `Cris(V/S|_W)` vanishes in degrees `> d`, the cohomology of
`RΓ(Cris(X/S), F) ∈ D⁺(Mod_A)` vanishes in every degree `j ≥ d + n`. -/
theorem isZero_homology_moduleULiftDerivedGlobalSections_of_finiteCover
    [HasDerivedCategory.{w} (ModuleSheaf S)]
    [HasDerivedCategory.{w'} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
    (F : SheafOfModules.{u} (structureSheaf S)) (d n : ℕ) (U : Fin n → S.X.Opens)
    (hcov : ⨆ i, U i = ⊤)
    (hU : ∀ s : Finset (Fin n), s.Nonempty →
      ∃ (W : S.S.scheme.Opens) (hVW : (⨅ i ∈ s, U i) ≤ sourceToBase S ⁻¹ᵁ W),
        ∀ j : ℕ, d < j → Subsingleton (cohomology (restrict S W (⨅ i ∈ s, U i) hVW)
          ((smallExtendAbelianRestriction S W (⨅ i ∈ s, U i) hVW).obj (abelianSheaf F)) j))
    (j : ℤ) (hj : (d : ℤ) + n ≤ j) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) j).obj
      (moduleULiftDerivedGlobalSections S F)) := by
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, j = (i : ℤ) := ⟨j.toNat, by omega⟩
  have hab := isZero_cohomologyFunctor_obj_of_finiteCover S (abelianSheaf F) d n U hcov hU i
    (by omega)
  have hforget : IsZero ((forgetBaseAction S).obj (moduleULiftCohomology S F i)) :=
    hab.of_iso (moduleULiftCohomologyIsoAbelian S F i)
  refine IsZero.of_iso ?_ (homologyModuleULiftDerivedGlobalSectionsIso S F i)
  exact ModuleCat.isZero_iff_subsingleton.2 (AddCommGrpCat.isZero_iff_subsingleton.1 hforget)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
