module

public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompGlue
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenCoverExactness

/-!
# The alternative construction of `f_!` as a cokernel

Let `f : X ⟶ Y` be a locally quasi-finite morphism in a big étale site. The Čech complex of an
open covering `X = ⋃_{i ∈ I} X_i` of Stacks 0F5H is exact, so its degree-zero term `f_!` is the
cokernel of its penultimate differential:

`f_! F = Coker(⊕_{i₀,i₁} f_{i₀i₁,!} F|_{X_{i₀i₁}} ⟶ ⊕_{i₀} f_{i₀,!} F|_{X_{i₀}})`.

Since `X` is covered by its affine opens, and an open of `X` contained in an affine open is
separated over `Y`, the covering may be chosen so that every restriction `f_{i₀…i_p}` is
separated; the terms of the complex are then the direct image with compact support of a separated
morphism, which is the proper-support construction of Section 0F4W. The displayed cokernel may
therefore be taken as the *definition* of `f_!`, which is the alternative construction of
Stacks 0F5I. The differential and the cokernel are computed in the category of functors on
abelian sheaves, so the construction produces `f_!` as a functor and not only objectwise.

## Main results

* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.exists_isSeparated_openCover` — a locally
  quasi-finite morphism admits an open covering of its source, by affine opens, along which every
  restriction `f_{i₀…i_p}` is separated.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechFamilyIsoProperSupport` — along such a
  covering each term of the Čech complex is the proper-support construction of Section 0F4W.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechComplexObj_isColimit_cokernel` — `f_! F` is
  the cokernel of the penultimate differential of the complex of `F`.
* `AlgebraicGeometry.SmallEtale.OpenCoverShriek.cechComplex_isColimit_cokernel` — the functor
  `f_!` is the cokernel of the penultimate differential of the complex of functors.

## Implementation notes

Exactness of the Čech complex is available objectwise (Stacks 0F5H, `cechComplexObj_acyclic`), and
a cokernel is read off from it at an index where the complex is exact and the outgoing differential
is epi: exactness in degree zero makes the last differential epi, because the differential leaving
degree zero of a chain complex indexed by `ℕ` is zero, and exactness in degree one then exhibits
degree zero as the cokernel of the differential from degree two.

The passage from the objectwise cokernel to the cokernel of functors is not a colimit-reflection
argument. The factoring morphism is assembled from the objectwise ones, its naturality being
obtained by cancelling the last differential, which is epi at every abelian sheaf; uniqueness is
that same cancellation.

## References

* [Stacks Project, Tag 0F5I](https://stacks.math.columbia.edu/tag/0F5I)
* [Stacks Project, Tag 0F5H](https://stacks.math.columbia.edu/tag/0F5H)
* [Stacks Project, Tag 0F6N](https://stacks.math.columbia.edu/tag/0F6N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.SmallEtale.OpenCoverShriek

section SeparatedCover

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- An open subscheme of `X` contained in an open which is affine is separated over `Y`: it is an
open immersion, hence separated, over an affine open which is itself separated over `Y`. -/
public theorem isSeparated_openSchemeι_comp_of_le {V W : (B.inclusion.obj X).Opens} (h : V ≤ W)
    (hW : IsAffineOpen W) :
    IsSeparated (B.inclusion.map (openSchemeι B V ≫ f)) := by
  have : IsSeparated (B.inclusion.map (openSchemeι B W ≫ f)) := isSeparated_compCover B f W hW
  have : IsSeparated (B.inclusion.map (openSchemeLE B h)) := IsSeparated.isSeparated_of_mono _
  have he : openSchemeLE B h ≫ openSchemeι B W ≫ f = openSchemeι B V ≫ f := by
    rw [← Category.assoc, openSchemeLE_ι]
  rw [← he]
  infer_instance

variable {I : Type (max (u + 1) v)} (U : I → (B.inclusion.obj X).Opens)

/-- The intersection cut out by a tuple of indices is contained in the open of each entry. -/
public theorem coverOpen_le {n : ℕ} (t : Fin n → I) (k : Fin n) :
    coverOpen B U t ≤ U (t k) :=
  iInf_le _ k

/-- Along a covering by affine opens every restriction `f_{i₀…i_p}` is separated. -/
public theorem isSeparated_coverOpen (hU : ∀ i, IsAffineOpen (U i)) {n : ℕ}
    (t : Fin (n + 1) → I) :
    IsSeparated (B.inclusion.map (openSchemeι B (coverOpen B U t) ≫ f)) :=
  isSeparated_openSchemeι_comp_of_le B f (coverOpen_le B U t 0) (hU (t 0))

/-- **Stacks 0F5I.** A locally quasi-finite morphism `f : X ⟶ Y` admits an open covering
`X = ⋃_{i ∈ I} X_i` such that every restriction `f_{i₀…i_p} : X_{i₀…i_p} ⟶ Y` is separated: the
covering of `X` by its affine opens is one. -/
@[stacks 0F5I "the covering with every restriction separated, by affine opens"]
public theorem exists_isSeparated_openCover :
    ∃ (J : Type (max (u + 1) v)) (V : J → (B.inclusion.obj X).Opens),
      (⨆ j, V j) = ⊤ ∧ (∀ j, IsAffineOpen (V j)) ∧
        ∀ {n : ℕ} (t : Fin (n + 1) → J),
          IsSeparated (B.inclusion.map (openSchemeι B (coverOpen B V t) ≫ f)) := by
  refine ⟨ULift.{max (u + 1) v} (B.inclusion.obj X).affineOpens, fun j => j.down, ?_,
    fun j => j.down.2, ?_⟩
  · rw [iSup_ulift]
    exact iSup_affineOpens_eq_top _
  · exact fun t => isSeparated_coverOpen B f _ (fun j => j.down.2) t

end SeparatedCover

section Terms

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  {I : Type (max (u + 1) v)} (U : I → (B.inclusion.obj X).Opens)

/-- **Stacks 0F5I.** Along a covering by affine opens the term of the Čech complex at a tuple of
indices is the proper-support direct image of Section 0F4W: the restriction `f_{i₀…i_p}` is
separated, so the two models of the direct image with compact support agree on it by
Stacks 0F6N. -/
@[stacks 0F5I "each term is the construction of Section 0F4W, the restrictions being separated"]
public def cechFamilyIsoProperSupport (hU : ∀ i, IsAffineOpen (U i)) {n : ℕ}
    (t : Fin (n + 1) → I) :
    cechFamily.{u, v} B f U (n + 1) t ≅
      openRestriction.{u, v} B (openSchemeι B (coverOpen B U t)) ⋙
        properSupportFunctor.{u, max (u + 1) v} B (openSchemeι B (coverOpen B U t) ≫ f) :=
  have := isSeparated_coverOpen B f U hU t
  Functor.isoWhiskerLeft _ (fShriekFunctorIsoProperSupport.{u, v} B _)

end Terms

section Cokernel

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  {I : Type (max (u + 1) v)} (U : I → (B.inclusion.obj X).Opens)

/-- The differentials of the Čech complex of an abelian sheaf are the components of the
differentials of the Čech complex of functors. -/
public theorem cechComplexObj_d_eq_app (m n : ℕ)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    (cechComplexObj.{u, v} B f U F).d m n = ((cechComplex.{u, v} B f U).d m n).app F :=
  rfl

/-- **Stacks 0F5I.** For an open covering of `X` and an abelian sheaf `F` on the small étale site
of `X`, the sheaf `f_! F` is the cokernel of the penultimate differential of the Čech complex of
Stacks 0F5H:

`f_! F = Coker(⊕_{i₀,i₁} f_{i₀i₁,!} F|_{X_{i₀i₁}} ⟶ ⊕_{i₀} f_{i₀,!} F|_{X_{i₀}})`. -/
@[stacks 0F5I "f_! F is the cokernel of the penultimate map of the complex of Stacks 0F5H"]
public def cechComplexObj_isColimit_cokernel (hU : (⨆ i, U i) = ⊤)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    IsColimit (CokernelCofork.ofπ ((cechAugMap.{u, v} B f U 1).app F)
      ((cechComplexObj.{u, v} B f U F).d_comp_d 2 1 0)) := by
  set K := cechComplexObj.{u, v} B f U F
  have hK : K.Acyclic := cechComplexObj_acyclic.{u, v} B f U hU F
  have hz : K.d 0 0 = 0 := K.shape 0 0 (by simp)
  have h0 : (K.sc' 1 0 0).Exact :=
    (K.exactAt_iff' 1 0 0 (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero).1 (hK 0)
  have h1 : (K.sc' 2 1 0).Exact :=
    (K.exactAt_iff' 2 1 0 (ChainComplex.prev ℕ 1) (ChainComplex.next_nat_succ 0)).1 (hK 1)
  have : Epi (K.sc' 2 1 0).g := h0.epi_f hz
  exact h1.gIsCokernel

/-- The augmentation of the Čech complex is an epimorphism at every abelian sheaf, being the
cokernel projection there. -/
public theorem epi_cechAugMap_one_app (hU : (⨆ i, U i) = ⊤)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    Epi ((cechAugMap.{u, v} B f U 1).app F) :=
  epi_of_isColimit_cofork (cechComplexObj_isColimit_cokernel.{u, v} B f U hU F)

/-- The augmentation of the Čech complex of functors is an epimorphism, being one at every
abelian sheaf. -/
public theorem epi_cechAugMap_one (hU : (⨆ i, U i) = ⊤) :
    Epi (cechAugMap.{u, v} B f U 1) := by
  have : ∀ F, Epi ((cechAugMap.{u, v} B f U 1).app F) :=
    epi_cechAugMap_one_app.{u, v} B f U hU
  exact NatTrans.epi_of_epi_app _

/-- **Stacks 0F5I.** The alternative construction of the functor `f_!` for a locally quasi-finite
morphism: for an open covering of `X` the functor `f_!` is the cokernel, in the category of
functors on abelian sheaves of the small étale site of `X`, of the penultimate differential of the
Čech complex of Stacks 0F5H. Taking this cokernel as the definition of `f_!` therefore recovers
`f_!` together with its functoriality. -/
@[stacks 0F5I "the functor f_! is that cokernel, the alternative construction"]
public def cechComplex_isColimit_cokernel (hU : (⨆ i, U i) = ⊤) :
    IsColimit (CokernelCofork.ofπ (cechAugMap.{u, v} B f U 1)
      ((cechComplex.{u, v} B f U).d_comp_d 2 1 0)) := by
  have := epi_cechAugMap_one.{u, v} B f U hU
  refine CokernelCofork.IsColimit.ofπ' _ _ (fun {A} k hk => ?_)
  have hkapp : ∀ F, (cechComplexObj.{u, v} B f U F).d 2 1 ≫ k.app F = 0 := fun F => by
    rw [cechComplexObj_d_eq_app]
    exact congrArg (fun η => NatTrans.app η F) hk
  let d := fun F => CokernelCofork.IsColimit.desc'
    (cechComplexObj_isColimit_cokernel.{u, v} B f U hU F) (k.app F) (hkapp F)
  have hfac : ∀ F, (cechAugMap.{u, v} B f U 1).app F ≫ (d F).1 = k.app F := fun F => (d F).2
  refine ⟨{ app := fun F => (d F).1, naturality := ?_ }, NatTrans.ext (funext hfac)⟩
  intro F G α
  have := epi_cechAugMap_one_app.{u, v} B f U hU F
  refine (cancel_epi ((cechAugMap.{u, v} B f U 1).app F)).1 ?_
  calc (cechAugMap.{u, v} B f U 1).app F ≫ (fShriekFunctor.{u, v} B f).map α ≫ (d G).1
      = ((cechAugMap.{u, v} B f U 1).app F ≫
          (fShriekFunctor.{u, v} B f).map α) ≫ (d G).1 := (Category.assoc _ _ _).symm
    _ = ((∐ cechFamily.{u, v} B f U 1).map α ≫
          (cechAugMap.{u, v} B f U 1).app G) ≫ (d G).1 := by
        rw [(cechAugMap.{u, v} B f U 1).naturality α]
    _ = (∐ cechFamily.{u, v} B f U 1).map α ≫
          ((cechAugMap.{u, v} B f U 1).app G ≫ (d G).1) := Category.assoc _ _ _
    _ = (∐ cechFamily.{u, v} B f U 1).map α ≫ k.app G := by rw [hfac G]
    _ = k.app F ≫ A.map α := k.naturality α
    _ = ((cechAugMap.{u, v} B f U 1).app F ≫ (d F).1) ≫ A.map α := by rw [hfac F]
    _ = (cechAugMap.{u, v} B f U 1).app F ≫ (d F).1 ≫ A.map α := Category.assoc _ _ _

end Cokernel

end AlgebraicGeometry.SmallEtale.OpenCoverShriek

end
