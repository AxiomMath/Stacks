module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Pullback
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.TwoIdealAdicQuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine

/-!
# Direct image of coherent adic systems along a closed immersion

Let `i : Z ⟶ X` be a closed immersion and `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals, with
inverse image `ℐ_Z = ℐ 𝒪_Z`. Termwise direct image carries `Coh(Z, ℐ_Z)` into `Coh(X, ℐ)`, and
it commutes with the completion functor of Stacks 0880.

Both statements rest on one isomorphism,
`Stacks.Coherent.pushforwardIdealPowerQuotientIso`:

`(i_* G) / ℐ ⁿ (i_* G) ≅ i_* (G / ℐ_Z ⁿ G)`.

It is assembled out of the two halves of the adjunction `i^* ⊣ i_*` rather than by comparing the
two subsheaves section by section. The left-hand side is annihilated by the ideal cutting out
`Z`, because `i_* G` is and annihilation passes to quotients, so the adjunction unit is
invertible on it ([Stacks, Tag 08KS]); inverse image commutes with ideal-power quotients, which
is `Stacks.Coherent.exists_functor_idealPowerQuotient_iso` for `i^*`; and the counit
`i^* i_* G ⟶ G` is invertible because `i_*` is fully faithful. The three isomorphisms compose to
the one above, and the triangle identity of the adjunction is what makes it compatible with the
quotient projections.

## Main definitions

* `Stacks.Coherent.pushforwardIdealPowerQuotientIso` — direct image along a closed immersion
  commutes with the ideal-power quotient.
* `Stacks.Coherent.coherentAdicPushforwardClosed` — the functor
  `i_* : Coh(Z, ℐ_Z) ⥤ Coh(X, ℐ)`.
* `Stacks.Coherent.completionPushforwardIso` — **direct image commutes with completion**:
  `(i_* G) ^∧ ≅ i_* (G ^∧)`.

## Main results

* `Stacks.Coherent.pushforwardIdealPowerQuotientIso_π` — the isomorphism is normalized by the
  quotient projections.
* `Stacks.Coherent.isCoherentAdicSystem_pushforward_of_isClosedImmersion` — **termwise direct
  image of a coherent adic system along `ℐ_Z` is a coherent adic system along `ℐ`.**

## Implementation notes

The hypotheses are a closed immersion and local Noetherianity of the target; `Z` is then locally
Noetherian too, by `AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion`. No flatness is
assumed and no identification of closed subschemes: the flat statements of
`CoherentAdicSystem.PullbackEquivalence` carry both `[Flat f]` and invertibility of
`(𝒥.comapIso f).hom ≫ pullback.snd f 𝒥.subschemeι`, neither of which a closed immersion
satisfies, so they do not apply here.

Indices are shifted as everywhere in this directory: term `n` of a system represents the
source's `F_{n+1}` and is annihilated by `ℐ ⁿ⁺¹`.

## References

* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-! ### Direct image commutes with the ideal-power quotient -/

/-- The ideal sheaf cutting out `Z` annihilates a direct image along `i`, by the essential-image
criterion of [Stacks, Tag 08KS]. -/
public theorem idealPowerMultiple_ker_pushforward_eq_bot (G : Z.Modules) :
    idealPowerMultiple i.ker 1 ((Scheme.Modules.pushforward i).obj G) = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun U a ha m => ?_
  rw [pow_one] at ha
  exact (Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal i _).mp
    ((Stacks.ClosedImmersion.pushforward_essImage_iff i _).mp
      ((Scheme.Modules.pushforward i).obj_mem_essImage G)) U a ha m

/-- The adjunction unit is invertible at the ideal-power quotient of a direct image: that
quotient is still annihilated by the ideal cutting out `Z`, so [Stacks, Tag 08KS] applies. -/
public theorem isIso_unit_idealPowerQuotient_pushforward (I : X.IdealSheafData) (n : ℕ)
    (G : Z.Modules) [G.IsQuasicoherent] :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (idealPowerQuotient I n ((Scheme.Modules.pushforward i).obj G))) := by
  have _ : ((Scheme.Modules.pushforward i).obj G).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom i G inferInstance
  have hb : idealPowerMultiple i.ker 1
      (idealPowerQuotient I n ((Scheme.Modules.pushforward i).obj G)) = ⊥ :=
    idealPowerMultiple_idealPowerQuotient_eq_bot_of_eq_bot i.ker I 1 n _
      (idealPowerMultiple_ker_pushforward_eq_bot i G)
  refine Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero i _ ?_
  refine (Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal i _).mpr fun U a ha m => ?_
  exact affine_sections_annihilated_of_idealPowerMultiple_eq_bot hb U
    (by rw [pow_one]; exact ha) m

/-- **Direct image along a closed immersion commutes with the ideal-power quotient.**
For a quasi-coherent `𝒪_Z`-module `G`,

`(i_* G) / ℐ ⁿ (i_* G) ≅ i_* (G / ℐ_Z ⁿ G)`,

where `ℐ_Z = ℐ 𝒪_Z` is the inverse image of `ℐ`.

The isomorphism is the composite of the adjunction unit at the left-hand side, which is
invertible by `Stacks.Coherent.isIso_unit_idealPowerQuotient_pushforward`, the direct image of
the comparison of `Stacks.Coherent.exists_functor_idealPowerQuotient_iso` for `i^*`, and the
direct image of the ideal-power quotient of the counit `i^* i_* G ⟶ G`, which is invertible
because `i_*` is fully faithful. -/
public def pushforwardIdealPowerQuotientIso (I : X.IdealSheafData) (n : ℕ)
    (G : Z.Modules) [G.IsQuasicoherent] :
    idealPowerQuotient I n ((Scheme.Modules.pushforward i).obj G) ≅
      (Scheme.Modules.pushforward i).obj (idealPowerQuotient (I.comap i) n G) :=
  haveI := isIso_unit_idealPowerQuotient_pushforward i I n G
  haveI := Stacks.ClosedImmersion.full_pushforward i
  haveI := Stacks.ClosedImmersion.faithful_pushforward i
  asIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (idealPowerQuotient I n ((Scheme.Modules.pushforward i).obj G))) ≪≫
    (Scheme.Modules.pushforward i).mapIso
      ((exists_functor_idealPowerQuotient_iso (Scheme.Modules.pullback i) I (I.comap i) n
          ((Scheme.Modules.pushforward i).obj G)
          (fun {_} φ => pullback_idealPowerMultiple_comp_eq_zero_iff i I n _ φ)).choose ≪≫
        (idealPowerQuotientFunctor (I.comap i) n).mapIso
          (asIso ((Scheme.Modules.pullbackPushforwardAdjunction i).counit.app G)))

/-- **The comparison is normalized by the quotient projections.** -/
public theorem pushforwardIdealPowerQuotientIso_π (I : X.IdealSheafData) (n : ℕ)
    (G : Z.Modules) [G.IsQuasicoherent] :
    cokernel.π (C := X.Modules)
          (idealPowerMultiple I n ((Scheme.Modules.pushforward i).obj G)).ι ≫
        (pushforwardIdealPowerQuotientIso i I n G).hom =
      (Scheme.Modules.pushforward i).map
        (cokernel.π (C := Z.Modules) (idealPowerMultiple (I.comap i) n G).ι) := by
  have hex := exists_functor_idealPowerQuotient_iso (Scheme.Modules.pullback i) I (I.comap i) n
    ((Scheme.Modules.pushforward i).obj G)
    (fun {_} φ => pullback_idealPowerMultiple_comp_eq_zero_iff i I n _ φ)
  have hspec := hex.choose_spec
  have hunit := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality
    (cokernel.π (C := X.Modules)
      (idealPowerMultiple I n ((Scheme.Modules.pushforward i).obj G)).ι)
  have hq := idealPowerQuotientMap_π (I.comap i) (I.comap i) n n le_rfl
    ((Scheme.Modules.pullbackPushforwardAdjunction i).counit.app G)
  have htri := (Scheme.Modules.pullbackPushforwardAdjunction i).right_triangle_components
    (Y := G)
  have hdef : (pushforwardIdealPowerQuotientIso i I n G).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (idealPowerQuotient I n ((Scheme.Modules.pushforward i).obj G)) ≫
        (Scheme.Modules.pushforward i).map (hex.choose.hom ≫
          (idealPowerQuotientFunctor (I.comap i) n).map
            ((Scheme.Modules.pullbackPushforwardAdjunction i).counit.app G)) := rfl
  have hunit' : cokernel.π (C := X.Modules)
        (idealPowerMultiple I n ((Scheme.Modules.pushforward i).obj G)).ι ≫
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (idealPowerQuotient I n ((Scheme.Modules.pushforward i).obj G)) =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          ((Scheme.Modules.pushforward i).obj G) ≫
        (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map
          (cokernel.π (C := X.Modules)
            (idealPowerMultiple I n ((Scheme.Modules.pushforward i).obj G)).ι)) := hunit
  have hinner : (Scheme.Modules.pullback i).map (cokernel.π (C := X.Modules)
          (idealPowerMultiple I n ((Scheme.Modules.pushforward i).obj G)).ι) ≫
        (hex.choose.hom ≫ (idealPowerQuotientFunctor (I.comap i) n).map
          ((Scheme.Modules.pullbackPushforwardAdjunction i).counit.app G)) =
      (Scheme.Modules.pullbackPushforwardAdjunction i).counit.app G ≫
        cokernel.π (C := Z.Modules) (idealPowerMultiple (I.comap i) n G).ι :=
    by erw [← Category.assoc, hspec]; exact hq
  erw [hdef, ← Category.assoc, hunit', Category.assoc, ← Functor.map_comp, hinner,
    Functor.map_comp, ← Category.assoc, htri, Category.id_comp]
  rfl

/-! ### Direct image of a coherent adic system -/

/-- A direct image along `i` of a module annihilated by `ℐ_Z ⁿ` is annihilated by `ℐ ⁿ`: the
projection onto its `ℐ ⁿ`-quotient is invertible, being the direct image of an invertible
projection followed by the comparison isomorphism. -/
public theorem idealPowerMultiple_pushforward_eq_bot (I : X.IdealSheafData) (n : ℕ)
    (G : Z.Modules) [G.IsQuasicoherent]
    (hG : idealPowerMultiple (I.comap i) n G = ⊥) :
    idealPowerMultiple I n ((Scheme.Modules.pushforward i).obj G) = ⊥ := by
  have _ : IsIso (cokernel.π (C := Z.Modules) (idealPowerMultiple (I.comap i) n G).ι) :=
    isIso_cokernel_π_of_eq_bot _ hG
  have hiso : IsIso (cokernel.π (C := X.Modules)
      (idealPowerMultiple I n ((Scheme.Modules.pushforward i).obj G)).ι) := by
    have h : cokernel.π (C := X.Modules)
        (idealPowerMultiple I n ((Scheme.Modules.pushforward i).obj G)).ι =
        (Scheme.Modules.pushforward i).map
          (cokernel.π (C := Z.Modules) (idealPowerMultiple (I.comap i) n G).ι) ≫
          (pushforwardIdealPowerQuotientIso i I n G).inv := by
      rw [← pushforwardIdealPowerQuotientIso_π i I n G, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [h]
    infer_instance
  refine (submodule_ι_eq_zero_iff _).1 ?_
  have hz := cokernel.condition (C := X.Modules)
    (idealPowerMultiple I n ((Scheme.Modules.pushforward i).obj G)).ι
  have _ : Mono (cokernel.π (C := X.Modules)
    (idealPowerMultiple I n ((Scheme.Modules.pushforward i).obj G)).ι) := inferInstance
  exact (cancel_mono (cokernel.π (C := X.Modules)
    (idealPowerMultiple I n ((Scheme.Modules.pushforward i).obj G)).ι)).1
      (hz.trans (zero_comp (C := X.Modules)).symm)

/-- **Termwise direct image along a closed immersion carries `Coh(Z, ℐ_Z)` into `Coh(X, ℐ)`.**

Coherence of each term is [Stacks, Tag 087T]; annihilation and the quotient clause are both read
off `Stacks.Coherent.pushforwardIdealPowerQuotientIso`, which identifies the `ℐ ⁿ⁺¹`-quotient of
`i_* G_{n+1}` with the direct image of the `ℐ_Z ⁿ⁺¹`-quotient of `G_{n+1}`, compatibly with the
quotient projections. -/
public theorem isCoherentAdicSystem_pushforward_of_isClosedImmersion [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {G : ℕᵒᵖ ⥤ Z.Modules}
    (hG : IsCoherentAdicSystem (I.comap i) G) :
    IsCoherentAdicSystem I (G ⋙ Scheme.Modules.pushforward i) := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · have _ : (G.obj (op n)).IsCoherent := hG.isCoherent n
    exact isCoherent_pushforward_of_isClosedImmersion i (G.obj (op n))
  · have _ : (G.obj (op n)).IsQuasicoherent := hG.isQuasicoherent n
    exact idealPowerMultiple_pushforward_eq_bot i I (n + 1) (G.obj (op n))
      (hG.idealPowerMultiple_eq_bot n)
  · have _ : (G.obj (op (n + 1))).IsQuasicoherent := hG.isQuasicoherent (n + 1)
    refine ⟨pushforwardIdealPowerQuotientIso i I (n + 1) (G.obj (op (n + 1))) ≪≫
      (Scheme.Modules.pushforward i).mapIso (hG.quotientIso n), ?_⟩
    show cokernel.π (C := X.Modules) _ ≫
      (pushforwardIdealPowerQuotientIso i I (n + 1) (G.obj (op (n + 1)))).hom ≫
        (Scheme.Modules.pushforward i).map (hG.quotientIso n).hom = _
    rw [← Category.assoc, pushforwardIdealPowerQuotientIso_π, ← Functor.map_comp,
      hG.cokernel_π_comp_quotientIso n]
    rfl

/-- **The functor `i_* : Coh(Z, ℐ_Z) ⥤ Coh(X, ℐ)`** attached to a closed immersion. -/
public def coherentAdicPushforwardClosed [IsLocallyNoetherian X] (I : X.IdealSheafData) :
    CoherentAdicSystems (I.comap i) ⥤ CoherentAdicSystems I :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙
      (Functor.whiskeringRight _ _ _).obj (Scheme.Modules.pushforward i))
    (fun G => isCoherentAdicSystem_pushforward_of_isClosedImmersion i I G.property)

/-- The terms of the direct-image system are the direct images of the terms. -/
public theorem coherentAdicPushforwardClosed_obj_obj [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (G : CoherentAdicSystems (I.comap i)) (n : ℕᵒᵖ) :
    ((coherentAdicPushforwardClosed i I).obj G).obj.obj n =
      (Scheme.Modules.pushforward i).obj (G.obj.obj n) := rfl

/-! ### Direct image commutes with completion -/

/-- **Direct image along a closed immersion commutes with completion.** For a coherent
`𝒪_Z`-module `G`, the completion along `ℐ` of `i_* G` is the termwise direct image of the
completion of `G` along `ℐ_Z = ℐ 𝒪_Z`.

Each component is `Stacks.Coherent.pushforwardIdealPowerQuotientIso`, and naturality is the
compatibility of that isomorphism with the quotient projections, which are epimorphisms. -/
public def completionPushforwardTermIso [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf)
    (hG : ((Scheme.Modules.pushforward i).obj G.obj).IsCoherent) (n : ℕ) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    haveI : G.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj
    ((completionFunctor X I).obj
        ⟨(Scheme.Modules.pushforward i).obj G.obj, hG⟩).obj.obj (op n) ≅
      (Scheme.Modules.pushforward i).obj
        (((completionFunctor Z (I.comap i)).obj G).obj.obj (op n)) :=
  letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  haveI : G.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj
  eqToIso (completionFunctor_obj X I ⟨(Scheme.Modules.pushforward i).obj G.obj, hG⟩ n) ≪≫
    pushforwardIdealPowerQuotientIso i I (n + 1) G.obj ≪≫
    ((Scheme.Modules.pushforward i).mapIso
      (eqToIso (completionFunctor_obj Z (I.comap i) G n))).symm

/-- **The termwise comparison is normalized by the completion projections.** -/
public theorem completionPushforwardTermIso_completionProjection [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf)
    (hG : ((Scheme.Modules.pushforward i).obj G.obj).IsCoherent) (n : ℕ) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    haveI : G.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj
    completionProjection X I ⟨(Scheme.Modules.pushforward i).obj G.obj, hG⟩ n ≫
        (completionPushforwardTermIso i I G hG n).hom =
      (Scheme.Modules.pushforward i).map (completionProjection Z (I.comap i) G n) := by
  let : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  have : G.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj
  set M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
    ⟨(Scheme.Modules.pushforward i).obj G.obj, hG⟩ with hMdef
  have hcancel : eqToHom (completionFunctor_obj X I M n).symm ≫
      eqToHom (completionFunctor_obj X I M n) = 𝟙 _ := eqToHom_trans _ _
  exact (Category.assoc (obj := X.Modules) _ _ _).trans
    ((congrArg (fun z => cokernel.π (C := X.Modules)
          (idealPowerMultiple I (n + 1) M.obj).ι ≫ z)
        (((Category.assoc (obj := X.Modules) _ _ _).symm.trans
            (congrArg (fun z => z ≫ (pushforwardIdealPowerQuotientIso i I (n + 1) G.obj).hom ≫
              (Scheme.Modules.pushforward i).map
                (eqToHom (completionFunctor_obj Z (I.comap i) G n).symm)) hcancel)).trans
          (Category.id_comp (obj := X.Modules) _))).trans
      (((Category.assoc (obj := X.Modules) _ _ _).symm.trans
          (congrArg (fun z => z ≫ (Scheme.Modules.pushforward i).map
              (eqToHom (completionFunctor_obj Z (I.comap i) G n).symm))
            (pushforwardIdealPowerQuotientIso_π i I (n + 1) G.obj))).trans
        ((Scheme.Modules.pushforward i).map_comp _ _).symm))

/-- **Direct image along a closed immersion commutes with completion.** -/
public def completionPushforwardIso [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf)
    (hG : ((Scheme.Modules.pushforward i).obj G.obj).IsCoherent) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    ((completionFunctor X I).obj ⟨(Scheme.Modules.pushforward i).obj G.obj, hG⟩).obj ≅
      ((completionFunctor Z (I.comap i)).obj G).obj ⋙ Scheme.Modules.pushforward i := by
  letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  have _ : G.obj.IsCoherent := G.property
  have _ : G.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj
  set M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
    ⟨(Scheme.Modules.pushforward i).obj G.obj, hG⟩ with hMdef
  have hkey := completionPushforwardTermIso_completionProjection i I G hG
  refine NatIso.ofComponents (fun n => completionPushforwardTermIso i I G hG n.unop) ?_
  intro m n f
  refine (Stacks.Algebraization.epi_completionProjection X I M m.unop).left_cancellation
    _ _ ?_
  refine Eq.trans (b := (Scheme.Modules.pushforward i).map
    (completionProjection Z (I.comap i) G n.unop)) ?_ (Eq.symm ?_)
  · exact (Category.assoc (obj := X.Modules) _ _ _).symm.trans
      ((congrArg (fun z => z ≫ _)
        (Stacks.Algebraization.completionProjection_map X I M f)).trans (hkey n.unop))
  · exact (Category.assoc (obj := X.Modules) _ _ _).symm.trans
      (((congrArg (fun z => z ≫
            (((completionFunctor Z (I.comap i)).obj G).obj ⋙
              Scheme.Modules.pushforward i).map f) (hkey m.unop)).trans
          ((Scheme.Modules.pushforward i).map_comp _ _).symm).trans
        (congrArg (Scheme.Modules.pushforward i).map
          (Stacks.Algebraization.completionProjection_map Z (I.comap i) G f)))

/-- **The comparison of `Stacks.Coherent.completionPushforwardIso` is normalized by the
completion projections**: at the level `n` the composite of the projection of `i_* G` with the
comparison is the direct image of the projection of `G`. -/
public theorem completionPushforwardIso_completionProjection [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf)
    (hG : ((Scheme.Modules.pushforward i).obj G.obj).IsCoherent) (n : ℕ) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    completionProjection X I ⟨(Scheme.Modules.pushforward i).obj G.obj, hG⟩ n ≫
        (completionPushforwardIso i I G hG).hom.app (op n) =
      (Scheme.Modules.pushforward i).map (completionProjection Z (I.comap i) G n) :=
  completionPushforwardTermIso_completionProjection i I G hG n

end Stacks.Coherent

end
