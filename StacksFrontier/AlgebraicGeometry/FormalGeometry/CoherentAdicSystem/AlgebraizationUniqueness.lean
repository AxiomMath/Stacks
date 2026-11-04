module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.CompletionKernelFaithful
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Algebraize

/-!
# The uniqueness clause of Tag 0889, in the form the end of Tag 088A needs

[Stacks, Tag 0889] part (1) algebraizes a map `α : (F_n) ⟶ G ^∧` into a triple `(F, a, β)` and
asserts that the triple is unique up to a unique isomorphism. The library states the uniqueness
clause through the canonical map `F ⟶ lim F_n` of
`Stacks.Algebraization.completionToLimit`, which is the form the proof produces it in. The end
of the proof of [Stacks, Tag 088A] needs the equivalent statement about the *completion* of the
comparison isomorphism: that `β ^∧ e = β'`.

This file carries that translation and the consequence the source draws from it: two coherent
adic systems mapping to a common one by maps with power-annihilated levelwise kernels and
cokernels, whose termwise completions are identified compatibly with those maps, are isomorphic.

## Main results

* `Stacks.Coherent.completion_map_hom_comp_eq_of_completionToLimit` — **the translation**: the
  `completionToLimit` form of the uniqueness clause gives `β ≫ e ^∧ = β'`.
* `Stacks.Coherent.exists_iso_of_algebraization_comparison` — **Tag 0889 (1), uniqueness, in the
  form the end of Tag 088A consumes**: two algebraizations of one map are identified by an
  isomorphism compatible with both the algebraized maps and the comparison isomorphisms.
* `Stacks.Coherent.nonempty_iso_of_completion_iso_over_power_annihilated` — **the last step of
  the proof of Tag 088A**: the termwise identifications assemble into an isomorphism of coherent
  adic systems.

## Implementation notes

The levelwise kernels and cokernels of the comparison `β ≫ a ^∧` are those of `a ^∧`, because
`β` is an isomorphism; they are annihilated by a power of the ideal by
`Stacks.Coherent.completion_map_term_annihilated`, which is the remark of [Stacks, Tag 0888].
This is what makes `Stacks.Algebraization.exists_unique_algebraization_of_isNoetherian`
applicable to the comparison attached to a given triple.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-! ### From the limit form of the uniqueness clause to the completion form -/

/-- The projection onto a term of a completion, read through the map to the limit. -/
public theorem completionProjection_comp_limMap_π (I : X.IdealSheafData)
    (Fsys : CoherentAdicSystems I)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (γ : Fsys.obj ≅ ((completionFunctor X I).obj G).obj) (n : ℕᵒᵖ) :
    completionProjection X I G n.unop ≫ γ.inv.app n =
      (completionToLimit X I G ≫ limMap (C := X.Modules) γ.inv) ≫
        limit.π (C := X.Modules) Fsys.obj n :=
  calc completionProjection X I G n.unop ≫ γ.inv.app n
      = (completionToLimit X I G ≫
          limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj n) ≫ γ.inv.app n :=
        congrArg (fun z => z ≫ γ.inv.app n) (completionToLimit_projection X I G n).symm
    _ = completionToLimit X I G ≫
          (limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj n ≫ γ.inv.app n) :=
        Category.assoc _ _ _
    _ = completionToLimit X I G ≫
          (limMap (C := X.Modules) γ.inv ≫ limit.π (C := X.Modules) Fsys.obj n) :=
        congrArg (fun z => completionToLimit X I G ≫ z) (limMap_π γ.inv n).symm
    _ = (completionToLimit X I G ≫ limMap (C := X.Modules) γ.inv) ≫
          limit.π (C := X.Modules) Fsys.obj n := (Category.assoc _ _ _).symm

/-- **The uniqueness clause of [Stacks, Tag 0889], translated.** If a map `c : F ⟶ F'` of
coherent modules is compatible with two identifications `β`, `β'` of a coherent adic system with
the completions of `F` and `F'`, in the sense that it respects the canonical maps to the limit,
then its completion carries `β` to `β'`. -/
public theorem completion_map_hom_comp_eq_of_completionToLimit (I : X.IdealSheafData)
    (Fsys : CoherentAdicSystems I)
    {F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (β : Fsys.obj ≅ ((completionFunctor X I).obj F).obj)
    (β' : Fsys.obj ≅ ((completionFunctor X I).obj F').obj)
    (c : F ⟶ F')
    (hc : c.hom ≫ (completionToLimit X I F' ≫ limMap (C := X.Modules) β'.inv) =
      completionToLimit X I F ≫ limMap (C := X.Modules) β.inv) :
    β.hom ≫ ((completionFunctor X I).map c).hom = β'.hom :=
  (completionMap_comp_eq_iff_limMap I c β β').2 hc

/-! ### Two algebraizations of one map are identified -/

/-- **[Stacks, Tag 0889] (1), the uniqueness clause in the form the end of [Stacks, Tag 088A]
consumes.** Let `(F_n)` be a coherent adic system along `ℐ`, let `G` be a coherent
`𝒪_X`-module, and let `(F, a, β)` and `(F', a', β')` be two algebraizations of one map
`(F_n) ⟶ G ^∧` — coherent modules with maps to `G` whose kernels and cokernels are annihilated
by a power of `ℐ`, identifications of `(F_n)` with their completions, and the common
factorization. Then there is an isomorphism `e : F ≅ F'` with `e ≫ a' = a` and
`β ≫ e ^∧ = β'`. -/
public theorem exists_iso_of_algebraization_comparison [IsNoetherian X] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : CoherentAdicSystems I)
    {F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (a : F ⟶ G) (a' : F' ⟶ G)
    (β : Fsys ≅ (completionFunctor X I).obj F)
    (β' : Fsys ≅ (completionFunctor X I).obj F')
    (hk : IsPowerAnnihilated I (kernel (C := X.Modules) a.hom))
    (hc : IsPowerAnnihilated I (cokernel (C := X.Modules) a.hom))
    (hk' : IsPowerAnnihilated I (kernel (C := X.Modules) a'.hom))
    (hc' : IsPowerAnnihilated I (cokernel (C := X.Modules) a'.hom))
    (hcomp : β.hom ≫ (completionFunctor X I).map a =
      β'.hom ≫ (completionFunctor X I).map a') :
    ∃ e : F ≅ F', e.hom ≫ a' = a ∧
      β.hom ≫ (completionFunctor X I).map e.hom = β'.hom := by
  have hann : IsKernelCokernelAnnihilatedByPower I
      (((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso β).hom ≫
        ((completionFunctor X I).map a).hom) := by
    obtain ⟨s, hs⟩ := hk
    obtain ⟨r, hr⟩ := hc
    refine ⟨2 * (s + r + 1), by omega, fun k => ?_⟩
    have hterm := completion_map_term_annihilated I I a
      (idealPowerMultiple_eq_bot_of_le hs (show s ≤ s + r + 1 by omega))
      (idealPowerMultiple_eq_bot_of_le hr (show r ≤ s + r + 1 by omega)) k
    have hiso : IsIso (((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso β).hom.app (op k)) :=
      (((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso β).app (op k)).isIso_hom
    have : Epi (C := X.Modules)
        (((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso β).hom.app (op k)) :=
      inferInstance
    exact ⟨idealPowerMultiple_eq_bot_of_iso I
        (kernelIsIsoComp (C := X.Modules) _
          (((completionFunctor X I).map a).hom.app (op k)))
        (2 * (s + r + 1)) hterm.1,
      idealPowerMultiple_eq_bot_of_iso I
        (cokernelEpiComp (C := X.Modules) _
          (((completionFunctor X I).map a).hom.app (op k)))
        (2 * (s + r + 1)) hterm.2⟩
  obtain ⟨F₀, a₀, β₀, ⟨-, hk₀, hc₀⟩, huniq⟩ :=
    exists_unique_algebraization_of_isNoetherian I G Fsys
      (((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso β).hom ≫
        ((completionFunctor X I).map a).hom) hann
  obtain ⟨d₁', ⟨hd₁a', hd₁β⟩, -⟩ :=
    huniq F a ((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso β) rfl hk hc
  obtain ⟨d₂', ⟨hd₂a', hd₂β⟩, -⟩ :=
    huniq F' a' ((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso β')
      (congrArg (fun φ : Fsys ⟶ (completionFunctor X I).obj G => φ.hom) hcomp) hk' hc'
  let d₁ := (ObjectProperty.ι
    (fun P : _root_.SheafOfModules.{u} X.ringCatSheaf => P.IsCoherent)).mapIso d₁'
  let d₂ := (ObjectProperty.ι
    (fun P : _root_.SheafOfModules.{u} X.ringCatSheaf => P.IsCoherent)).mapIso d₂'
  have hd₁a : d₁.hom ≫ a.hom = a₀.hom := congrArg (fun k => k.hom) hd₁a'
  have hd₂a : d₂.hom ≫ a'.hom = a₀.hom := congrArg (fun k => k.hom) hd₂a'
  have hd₁l : d₁.hom ≫ (completionToLimit X I F ≫ limMap (C := X.Modules)
      ((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso β).inv) =
        completionToLimit X I F₀ ≫ limMap (C := X.Modules) β₀.inv :=
    (Stacks.Algebraization.completionMap_comp_eq_iff_limMap I d₁'.hom β₀ _).1 hd₁β
  have hd₂l : d₂.hom ≫ (completionToLimit X I F' ≫ limMap (C := X.Modules)
      ((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso β').inv) =
        completionToLimit X I F₀ ≫ limMap (C := X.Modules) β₀.inv :=
    (Stacks.Algebraization.completionMap_comp_eq_iff_limMap I d₂'.hom β₀ _).1 hd₂β
  refine ⟨(ObjectProperty.fullyFaithfulι
      (fun P : _root_.SheafOfModules.{u} X.ringCatSheaf => P.IsCoherent)).preimageIso
    (d₁.symm ≪≫ d₂), ObjectProperty.hom_ext _ ?_, ObjectProperty.hom_ext _ ?_⟩
  · exact (congrArg (d₁.inv ≫ ·) (hd₂a.trans hd₁a.symm)).trans (d₁.inv_hom_id_assoc _)
  · refine completion_map_hom_comp_eq_of_completionToLimit I Fsys
      ((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso β)
      ((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso β') _ ?_
    exact (Category.assoc (obj := X.Modules) _ _ _).trans
      ((congrArg (d₁.inv ≫ ·) (hd₂l.trans hd₁l.symm)).trans (d₁.inv_hom_id_assoc _))

/-! ### The last step of the proof of Tag 088A -/

/-- **The last step of the proof of [Stacks, Tag 088A].** Let `(F_n)`, `(F'_n)` and `(H_n)` be
coherent adic systems along `ℐ`, let `α : (F_n) ⟶ (H_n)` and `α' : (F'_n) ⟶ (H_n)` be morphisms
whose termwise kernels and cokernels are annihilated by powers of `𝒦`, and suppose the towers of
`𝒦`-completions of the terms of `(F_n)` and `(F'_n)` are identified compatibly with `α` and
`α'`. Then `(F'_n) ≅ (F_n)`. -/
public theorem nonempty_iso_of_completion_iso_over_power_annihilated [IsNoetherian X]
    (I K : X.IdealSheafData) {F F' H : CoherentAdicSystems I} (α : F ⟶ H) (α' : F' ⟶ H)
    (hαk : ∀ n : ℕ, IsPowerAnnihilated K
      (kernel (C := X.Modules) (((coherentAdicTerms I).map α).app (op n)).hom))
    (hαc : ∀ n : ℕ, IsPowerAnnihilated K
      (cokernel (C := X.Modules) (((coherentAdicTerms I).map α).app (op n)).hom))
    (hα'k : ∀ n : ℕ, IsPowerAnnihilated K
      (kernel (C := X.Modules) (((coherentAdicTerms I).map α').app (op n)).hom))
    (hα'c : ∀ n : ℕ, IsPowerAnnihilated K
      (cokernel (C := X.Modules) (((coherentAdicTerms I).map α').app (op n)).hom))
    (d : (coherentAdicTerms I).obj F ⋙ completionFunctor X K ≅
      (coherentAdicTerms I).obj F' ⋙ completionFunctor X K)
    (hd : ∀ n : ℕ, (completionFunctor X K).map (((coherentAdicTerms I).map α).app (op n)) =
      (d.app (op n)).hom ≫
        (completionFunctor X K).map (((coherentAdicTerms I).map α').app (op n))) :
    Nonempty (F' ≅ F) := by
  have hex : ∀ n : ℕ, ∃ e : ((coherentAdicTerms I).obj F').obj (op n) ≅
      ((coherentAdicTerms I).obj F).obj (op n),
      e.hom ≫ ((coherentAdicTerms I).map α).app (op n) =
          ((coherentAdicTerms I).map α').app (op n) ∧
        (completionFunctor X K).map e.hom = d.inv.app (op n) := by
    intro n
    obtain ⟨e₀, he₀a, he₀b⟩ := exists_iso_of_algebraization_comparison K
      (((coherentAdicTerms I).obj H).obj (op n))
      ((completionFunctor X K).obj (((coherentAdicTerms I).obj F).obj (op n)))
      (((coherentAdicTerms I).map α').app (op n))
      (((coherentAdicTerms I).map α).app (op n))
      (d.app (op n)) (Iso.refl _) (hα'k n) (hα'c n) (hαk n) (hαc n)
      ((hd n).symm.trans (Category.id_comp _).symm)
    refine ⟨e₀, he₀a, ?_⟩
    exact (Iso.hom_comp_eq_id (d.app (op n))).1 he₀b
  choose e he hCe using hex
  have hnat : ∀ n : ℕ,
      F'.obj.map (homOfLE (Nat.le_add_right n 1)).op ≫ (e n).hom.hom =
        (e (n + 1)).hom.hom ≫ F.obj.map (homOfLE (Nat.le_add_right n 1)).op := by
    intro n
    obtain ⟨t, ht⟩ := hαk n
    have hcoh : ((coherentAdicTerms I).obj F').map (homOfLE (Nat.le_add_right n 1)).op ≫
        (e n).hom = (e (n + 1)).hom ≫
          ((coherentAdicTerms I).obj F).map (homOfLE (Nat.le_add_right n 1)).op := by
      refine completion_map_injective_over_map_with_annihilated_kernel K
        (((coherentAdicTerms I).map α).app (op n)) t ht ?_ ?_
      · simp only [Category.assoc, ((coherentAdicTerms I).map α).naturality]
        rw [reassoc_of% he (n + 1), he n, ((coherentAdicTerms I).map α').naturality]
      · rw [Functor.map_comp, Functor.map_comp, hCe n, hCe (n + 1)]
        exact d.inv.naturality _
    exact congrArg (fun f => f.hom) hcoh
  exact ⟨(ObjectProperty.fullyFaithfulι (IsCoherentAdicSystem I)).preimageIso
    (NatIso.ofComponents (fun y => (ObjectProperty.ι _).mapIso (e y.unop))
      (fun g => (NatTrans.ofOpSequence (fun n => (e n).hom.hom) hnat).naturality g))⟩

end Stacks.Coherent

end
