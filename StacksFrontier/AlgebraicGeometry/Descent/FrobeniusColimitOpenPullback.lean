module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitOpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFunctorial

/-!
# The transition functor along an open immersion is restriction to the open subscheme

Let `p` be a prime, let `X` be a scheme in characteristic `p` and let `V` be an open of `X`. There
are two restriction functors on finite locally free `colim_F 𝒪_X`-modules, and nothing so far
related them:

* the **transition functor** of [Stacks, Tag 0EXE] of the open immersion `V.ι`, which is extension
  of scalars along `AlgebraicGeometry.frobeniusColimitStructureSheafHom`.  This is the functor the
  square comparison, the pasting law and the cube of
  `StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSquarePaste` speak;
* **`AlgebraicGeometry.frobeniusColimitModuleRestrict`**, slice restriction to `V` followed by the
  equivalence `AlgebraicGeometry.frobeniusColimitModuleOpenEquiv`. This is the functor the
  freeness transport `AlgebraicGeometry.exists_cover_free_frobeniusColimitModuleRestrict` speaks.

This file identifies them, so that the two halves of the trivialising-cover argument for
[Stacks, Tag 0EXD] meet.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitSiteRestrict`: restriction of a sheaf of modules over
  `colim_F 𝒪_X` to the open subscheme `V`, realised as **pushforward along the open-image
  functor** of `V.ι` with the identification `colim_F 𝒪_V ≅ (colim_F 𝒪_X)|_V` as its morphism of
  sheaves of rings.
* `AlgebraicGeometry.frobeniusColimitSiteRestrictAdjunctionOfIso`: **restriction along an
  arbitrary morphism of schemes with an adjoint site functor is left adjoint to pushforward along
  it**, given a presentation of the comorphism as the counit of that adjunction and an
  identification of the two Frobenius colimits compatible with the stages.  This is the general
  form; the two cases the development needs are instances of it.
* `AlgebraicGeometry.frobeniusColimitSiteRestrictAdjunction`: **that functor is left adjoint to
  pushforward along `V.ι`**, the instance of the preceding at the open immersion `V.ι`.
* `AlgebraicGeometry.frobeniusColimitSiteRestrictIsoPullback`: **hence it is the transition
  functor**, by uniqueness of left adjoints.

## Main results

* `AlgebraicGeometry.frobeniusColimitι_comp_frobeniusColimitRingSheafRestrictIso_hom`: **the
  open-subscheme identification of `colim_F 𝒪` is compatible with the stage coprojections.** This
  is the only piece of content in the whole identification: a morphism out of `colim_F 𝒪_X` is
  determined by its restrictions to the stages of the colimit, and this computes them.
* `CategoryTheory.Limits.comp_transpose_eq_id_of_isIso`: the second compatibility hypothesis of
  `CategoryTheory.SheafOfModules.pushforwardPushforwardAdj` follows from the first when the
  morphism of sheaves of rings is invertible.
* `CategoryTheory.SheafOfModules.pushforwardAdjOfIsIso`: consequently, **for an adjoint pair of
  continuous site functors and an invertible morphism of sheaves of rings the counit condition
  alone makes the two pushforwards adjoint** — the whole of the adjunction above that is not
  about the Frobenius colimit.

## Implementation notes

**Why an adjunction and not a computation.** Mathlib defines
`CategoryTheory.SheafOfModules.pullback` as the left adjoint of the pushforward, so there is no
formula for it to be compared against. What there is instead is Mathlib's
`CategoryTheory.SheafOfModules.pushforwardPushforwardAdj`: for an *adjoint pair* of continuous site
functors the two pushforwards are adjoint. The open-image functor `V.ι ''ᵁ -` is left adjoint to
`V.ι ⁻¹ᵁ -`, so the restriction functor built here is a left adjoint to the same pushforward as
the transition functor is, and `CategoryTheory.Adjunction.leftAdjointUniq` finishes. This is the
route `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` takes for the structure sheaf
and `AlgebraicGeometry.SheafOfModules.overFunctorIsoPullback` for a ringed space; the only new
input for the Frobenius colimit is the stage compatibility above.

**Why the adjunction is stated at an arbitrary morphism of schemes.** Generality here is cheap
and specialisation downstream is dear.  The nested-opens case — the inclusion of `U ≤ V` as open
subschemes of an ambient `X` — is not literally of the form `V.ι`, and the two presentations of
its site functor agree only at default transparency, so bridging it downstream means identifying
them inside one term, which exhausts the heartbeat budget.
`AlgebraicGeometry.frobeniusColimitSiteRestrictAdjunctionOfIso` takes the comparison `σ` of the
structure sheaves as a parameter, and both cases are then instances with nothing to identify.

**Why the two compatibility hypotheses are proved by the universal property.** Both are equations
between morphisms whose source is the sequential colimit `colim_F 𝒪_X`, respectively
`colim_F 𝒪_V`, so neither can be checked on sections — the colimit of sheaves is a sheafification
and its sections are not a colimit of sections. `CategoryTheory.Limits.endoColimit_hom_ext` reduces
each to a stagewise statement about the structure sheaves, which *is* a computation on sections.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Frobenius

universe u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}

/-- **Restriction to a slice site carries the stage-`n` coprojection to the stage-`n`
coprojection.** -/
lemma map_ringSheafEndoColimitι_comp_ringSheafEndoColimitOverIso_hom (ψ : S ⟶ S) (U : C)
    (n : ℕ) :
    (J.overPullback RingCat.{u} U).map (ringSheafEndoColimitι ψ n) ≫
        (ringSheafEndoColimitOverIso ψ U).hom =
      ringSheafEndoColimitι ((J.overPullback RingCat.{u} U).map ψ) n := by
  have : PreservesColimitsOfSize.{0, 0} (J.overPullback RingCat.{u} U) :=
    GrothendieckTopology.preservesColimits_overPullback.{0, 0} J RingCat.{u} U
  exact map_endoColimitι_comp_endoColimitCompIso_hom ψ _ n

/-- **An equivalence of categories of sheaves of rings carries the stage-`n` coprojection to the
stage-`n` coprojection.** -/
lemma map_ringSheafEndoColimitι_comp_ringSheafEndoColimitEquivIso_hom {D : Type u}
    [Category.{u} D] {K : GrothendieckTopology D} (ψ : S ⟶ S)
    (E : Sheaf J RingCat.{u} ≌ Sheaf K RingCat.{u}) (n : ℕ) :
    E.functor.map (ringSheafEndoColimitι ψ n) ≫ (ringSheafEndoColimitEquivIso ψ E).hom =
      ringSheafEndoColimitι (E.functor.map ψ) n := by
  have : PreservesColimitsOfSize.{0, 0} E.functor :=
    Adjunction.leftAdjoint_preservesColimits E.toAdjunction
  exact map_endoColimitι_comp_endoColimitCompIso_hom ψ _ n

/-- The coprojections of the colimits along two equal endomorphisms agree across the transport. -/
lemma ringSheafEndoColimitι_comp_eqToHom {ψ ψ' : S ⟶ S} (h : ψ = ψ') (n : ℕ) :
    ringSheafEndoColimitι ψ n ≫
        eqToHom (congrArg (fun χ : S ⟶ S => ringSheafEndoColimit χ) h) =
      ringSheafEndoColimitι ψ' n := by
  subst h
  simp

/-- **The second compatibility of an adjoint pair of pushforwards follows from the first when the
ring map is invertible.**  If `φ : S ⟶ L.obj R` is an isomorphism and a morphism
`η : R ⟶ Rt.obj (L.obj R)` satisfying the left triangle identity factors as `ψ` followed by
`Rt.map φ`, then `φ` and the transpose `L.map ψ ≫ ε S` of `ψ` are mutually inverse.

This is stated for a bare unit-counit pair rather than for a
`CategoryTheory.Adjunction`, because the pair that
`CategoryTheory.SheafOfModules.pushforwardPushforwardAdj` consumes is given by whiskering and not
as an adjunction. -/
lemma comp_transpose_eq_id_of_isIso {A : Type*} [Category A] {B : Type*} [Category B]
    {L : A ⥤ B} {Rt : B ⥤ A} {R : A} {S : B} (η : R ⟶ Rt.obj (L.obj R))
    (ε : ∀ b : B, L.obj (Rt.obj b) ⟶ b)
    (hnat : ∀ {b b' : B} (f : b ⟶ b'), L.map (Rt.map f) ≫ ε b' = ε b ≫ f)
    (htri : L.map η ≫ ε (L.obj R) = 𝟙 (L.obj R))
    (φ : S ⟶ L.obj R) [IsIso φ] (ψ : R ⟶ Rt.obj S) (h : η = ψ ≫ Rt.map φ) :
    φ ≫ L.map ψ ≫ ε S = 𝟙 S := by
  have hT : (L.map ψ ≫ ε S) ≫ φ = 𝟙 (L.obj R) := by
    rw [Category.assoc, ← hnat φ, ← Category.assoc, ← L.map_comp, ← h, htri]
  have hT' : L.map ψ ≫ ε S = inv φ := by
    rw [← Category.id_comp (inv φ), ← hT, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hT', IsIso.hom_inv_id]

end CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D} {G : D ⥤ C}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [F.IsContinuous J K] [G.IsContinuous K J]

/-- **For an adjoint pair of continuous site functors and an *invertible* morphism of sheaves of
rings, the counit condition alone makes the two pushforwards adjoint.**

`CategoryTheory.SheafOfModules.pushforwardPushforwardAdj` asks two compatibilities of the pair
`(φ, ψ)` of morphisms of sheaves of rings; `h1`, the one about the counit of the site-level
adjunction, is the first of them, and when `φ` is invertible the second follows from it by
`CategoryTheory.Limits.comp_transpose_eq_id_of_isIso`, the transpose of `ψ` being forced to be
the inverse of `φ`.

Nothing here is about a scheme or a Frobenius colimit: the statement is at an arbitrary adjoint
pair of continuous functors of sites and an arbitrary pair of sheaves of rings, which is what
lets both the open-immersion case and the nested-opens case of
[Stacks, Tag 0EXE] be instances of it. -/
noncomputable def pushforwardAdjOfIsIso (adj : F ⊣ G)
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) [IsIso φ]
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj S)
    (h1 : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom) :
    pushforward.{u} φ ⊣ pushforward.{u} ψ := by
  let mkA : ∀ P : Sheaf K RingCat.{u},
      P ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj
        ((F.sheafPushforwardContinuous RingCat.{u} J K).obj P) :=
    fun P => ⟨Functor.whiskerRight (NatTrans.op adj.counit) P.obj⟩
  let mkB : ∀ Q : Sheaf J RingCat.{u},
      (F.sheafPushforwardContinuous RingCat.{u} J K).obj
        ((G.sheafPushforwardContinuous RingCat.{u} K J).obj Q) ⟶ Q :=
    fun Q => ⟨Functor.whiskerRight (NatTrans.op adj.unit) Q.obj⟩
  have hnatB : ∀ {P Q : Sheaf J RingCat.{u}} (α : P ⟶ Q),
      (F.sheafPushforwardContinuous RingCat.{u} J K).map
        ((G.sheafPushforwardContinuous RingCat.{u} K J).map α) ≫ mkB Q = mkB P ≫ α := by
    intro P Q α
    apply Sheaf.hom_ext
    ext W : 2
    exact (α.hom.naturality (adj.unit.app W.unop).op).symm
  have htri : ∀ P : Sheaf K RingCat.{u},
      (F.sheafPushforwardContinuous RingCat.{u} J K).map (mkA P) ≫
        mkB ((F.sheafPushforwardContinuous RingCat.{u} J K).obj P) = 𝟙 _ := by
    intro P
    apply Sheaf.hom_ext
    ext W x
    change (P.obj.map (adj.counit.app (F.obj W.unop)).op ≫
      P.obj.map (F.map (adj.unit.app W.unop)).op) x = x
    rw [← Functor.map_comp, ← op_comp, adj.left_triangle_components W.unop]
    exact CategoryTheory.Functor.map_id_apply P.obj (Opposite.op (F.obj W.unop)) x
  have hA : mkA R = ψ ≫ (G.sheafPushforwardContinuous RingCat.{u} K J).map φ :=
    Sheaf.hom_ext h1
  have hB : φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ ≫ mkB S = 𝟙 S :=
    comp_transpose_eq_id_of_isIso (mkA R) mkB (fun f => hnatB f) (htri R) φ ψ hA
  exact pushforwardPushforwardAdj adj φ ψ h1 (Sheaf.hom_ext_iff.mp hB)

end SheafOfModules

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p) (V : X.Opens)
  (hV : IsInCharacteristic V.toScheme p)

/-- Restriction of a sheaf of modules over `colim_F 𝒪_X` to the open subscheme `V`, realised as
pushforward along the open-image functor of `V.ι`. -/
noncomputable def frobeniusColimitSiteRestrict :
    _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX) ⥤
      _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf V.toScheme p hV) := by
  let H : Topology.IsOpenEmbedding (TopCat.Hom.hom V.ι.base) := Scheme.Hom.isOpenEmbedding V.ι
  letI : H.isOpenMap.functor.IsContinuous
      (Opens.grothendieckTopology (V.toScheme : TopCat))
      (Opens.grothendieckTopology (X : TopCat)) := H.functor_isContinuous
  exact _root_.SheafOfModules.pushforward (F := H.isOpenMap.functor)
    (frobeniusColimitRingSheafRestrictIso X p hX V hV).inv

/-- **The open-subscheme identification of `colim_F 𝒪` is compatible with the stage
coprojections.**  Restricting the stage-`n` coprojection of `colim_F 𝒪_X` to `V` and transporting
along `AlgebraicGeometry.frobeniusColimitRingSheafRestrictIso` gives the stage-`n` coprojection of
`colim_F 𝒪_V`.

This is the one piece of content in the identification of the transition functor of
[Stacks, Tag 0EXE] along an open immersion with restriction to the open subscheme: both sides are
morphisms out of a sequential colimit, so a morphism out of `colim_F 𝒪_X` is determined by its
restrictions to the stages, and this lemma is what computes them. -/
lemma frobeniusColimitι_comp_frobeniusColimitRingSheafRestrictIso_hom (n : ℕ) :
    V.sheafRestrict.map (frobeniusColimitι X p hX n) ≫
        (frobeniusColimitRingSheafRestrictIso X p hX V hV).hom =
      frobeniusColimitι V.toScheme p hV n := by
  have h1 : ((Opens.grothendieckTopology (X : TopCat)).overPullback RingCat.{u} V).map
          (frobeniusColimitι X p hX n) ≫
        (frobeniusColimitRingSheafOverIso X p hX V).hom =
      ringSheafEndoColimitι
        (((Opens.grothendieckTopology (X : TopCat)).overPullback RingCat.{u} V).map
          (frobeniusRingSheafOnOpensHom X p hX)) n :=
    map_ringSheafEndoColimitι_comp_ringSheafEndoColimitOverIso_hom _ V n
  have h2 : (Opens.sheafEquivOver V (A := RingCat.{u})).functor.map
          (ringSheafEndoColimitι
            (((Opens.grothendieckTopology (X : TopCat)).overPullback RingCat.{u} V).map
              (frobeniusRingSheafOnOpensHom X p hX)) n) ≫
        (ringSheafEndoColimitEquivIso
            (((Opens.grothendieckTopology (X : TopCat)).overPullback RingCat.{u} V).map
              (frobeniusRingSheafOnOpensHom X p hX))
            (Opens.sheafEquivOver V (A := RingCat.{u}))).hom =
      ringSheafEndoColimitι
        ((Opens.sheafEquivOver V (A := RingCat.{u})).functor.map
          (((Opens.grothendieckTopology (X : TopCat)).overPullback RingCat.{u} V).map
            (frobeniusRingSheafOnOpensHom X p hX))) n :=
    map_ringSheafEndoColimitι_comp_ringSheafEndoColimitEquivIso_hom _ _ n
  -- The trailing morphism is handed in as a variable, so that the reassociation and the two
  -- coprojection formulas are applied in a goal whose type mentions only the site of `V`.
  have gen : ∀ {W : Sheaf (Opens.grothendieckTopology ↥V) RingCat.{u}}
      (t : ringSheafEndoColimit
          ((Opens.sheafEquivOver V (A := RingCat.{u})).functor.map
            (((Opens.grothendieckTopology (X : TopCat)).overPullback RingCat.{u} V).map
              (frobeniusRingSheafOnOpensHom X p hX))) ⟶ W),
      (Opens.sheafEquivOver V (A := RingCat.{u})).functor.map
            (((Opens.grothendieckTopology (X : TopCat)).overPullback RingCat.{u} V).map
              (frobeniusColimitι X p hX n)) ≫
          ((Opens.sheafEquivOver V (A := RingCat.{u})).functor.map
              (frobeniusColimitRingSheafOverIso X p hX V).hom ≫
            (ringSheafEndoColimitEquivIso
                (((Opens.grothendieckTopology (X : TopCat)).overPullback RingCat.{u} V).map
                  (frobeniusRingSheafOnOpensHom X p hX))
                (Opens.sheafEquivOver V (A := RingCat.{u}))).hom ≫ t) =
        ringSheafEndoColimitι
            ((Opens.sheafEquivOver V (A := RingCat.{u})).functor.map
              (((Opens.grothendieckTopology (X : TopCat)).overPullback RingCat.{u} V).map
                (frobeniusRingSheafOnOpensHom X p hX))) n ≫ t := by
    intro W t
    rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, h1, h2]
  have hdef : (frobeniusColimitRingSheafRestrictIso X p hX V hV).hom =
      (Opens.sheafEquivOver V (A := RingCat.{u})).functor.map
            (frobeniusColimitRingSheafOverIso X p hX V).hom ≫
          (ringSheafEndoColimitEquivIso
              (((Opens.grothendieckTopology (X : TopCat)).overPullback RingCat.{u} V).map
                (frobeniusRingSheafOnOpensHom X p hX))
              (Opens.sheafEquivOver V (A := RingCat.{u}))).hom ≫
            eqToHom (congrArg (fun ψ => ringSheafEndoColimit ψ)
              (sheafEquivOver_functor_map_frobeniusRingSheafOnOpensHom X p hX V hV)) :=
    Category.id_comp _
  refine Eq.trans ?_ (ringSheafEndoColimitι_comp_eqToHom
    (sheafEquivOver_functor_map_frobeniusRingSheafOnOpensHom X p hX V hV) n)
  exact (congrArg (fun t => (Opens.sheafEquivOver V (A := RingCat.{u})).functor.map
    (((Opens.grothendieckTopology (X : TopCat)).overPullback RingCat.{u} V).map
      (frobeniusColimitι X p hX n)) ≫ t) hdef).trans (gen _)

section General

variable {Y Z : Scheme.{u}} (p : ℕ) [Fact p.Prime] (f : Y ⟶ Z)
  (hY : IsInCharacteristic Y p) (hZ : IsInCharacteristic Z p)
  {F : Opens (Y : TopCat) ⥤ Opens (Z : TopCat)}
  [F.IsContinuous (Opens.grothendieckTopology (Y : TopCat))
    (Opens.grothendieckTopology (Z : TopCat))]

/-- **Restriction along an arbitrary morphism of schemes with an adjoint site functor is left
adjoint to pushforward along it**, for the Frobenius colimits of the structure sheaves.

Let `f : Y ⟶ Z` be a morphism of schemes in characteristic `p` and let `F` be a continuous
functor of the sites of opens left adjoint to `Opens.map f.base` — for an open immersion, the
open-image functor.  The data relating `F` to the two structure sheaves is a morphism
`σ : 𝒪_Y ⟶ F_* 𝒪_Z` presenting the comorphism of `f` as the counit of `adj` read on `𝒪_Z`
(`hstruct`), and an isomorphism `φ : colim_F 𝒪_Y ≅ F_* (colim_F 𝒪_Z)` compatible with `σ` on the
stages of the colimit (`hk`).  Then the pushforward along `F` with `φ` as its morphism of sheaves
of rings is left adjoint to pushforward along `f`.

**This is the general form of the identification, and the point of stating it generally.** Its
hypotheses mention only one open at a time, so both the open immersion `V.ι` of an open of `Z`
(`AlgebraicGeometry.frobeniusColimitSiteRestrictAdjunction`, where `σ` is the identity because
`𝒪_V` *is* `F_* 𝒪_Z`) and the inclusion `AlgebraicGeometry.Scheme.homOfLE` of a nested pair of
opens of an ambient scheme
(`AlgebraicGeometry.frobeniusColimitNestedSiteRestrictAdjunction`, where `σ` is the comparison of
the two ways of taking the image in the ambient scheme) are instances.  In the nested case the
two presentations of one site functor agree only at default transparency, so a proof that reduced
the nested case to the `V.ι` case downstream would have to identify them inside a single term,
which exhausts the heartbeat budget; stated at this altitude there is nothing to identify.

Both compatibility hypotheses of
`CategoryTheory.SheafOfModules.pushforwardPushforwardAdj` are equations between morphisms **out
of the sequential colimit** `colim_F 𝒪_Z`, so the one that is not automatic is proved by the
universal property: `CategoryTheory.Limits.endoColimit_hom_ext` reduces it to `hstruct` and `hk`,
which are statements about the structure sheaves and the stages. -/
noncomputable def frobeniusColimitSiteRestrictAdjunctionOfIso (adj : F ⊣ Opens.map f.base)
    (σ : Y.ringSheafOnOpens ⟶
      (F.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology (Y : TopCat))
        (Opens.grothendieckTopology (Z : TopCat))).obj Z.ringSheafOnOpens)
    (φ : frobeniusColimitRingSheaf Y p hY ≅
      (F.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology (Y : TopCat))
        (Opens.grothendieckTopology (Z : TopCat))).obj (frobeniusColimitRingSheaf Z p hZ))
    (hstruct : Functor.whiskerRight (NatTrans.op adj.counit) Z.ringSheafOnOpens.obj =
      f.ringSheafOnOpensHom.hom ≫ (Opens.map f.base).op.whiskerLeft σ.hom)
    (hk : ∀ n, σ ≫ (F.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology (Y : TopCat))
        (Opens.grothendieckTopology (Z : TopCat))).map (frobeniusColimitι Z p hZ n) =
      frobeniusColimitι Y p hY n ≫ φ.hom) :
    _root_.SheafOfModules.pushforward.{u} φ.hom ⊣
      _root_.SheafOfModules.pushforward.{u} (frobeniusColimitStructureSheafHom p f hY hZ) := by
  -- the unit of the site-level adjunction, at a sheaf of rings on `Z`
  let mkA : ∀ P : Sheaf (Opens.grothendieckTopology (Z : TopCat)) RingCat.{u},
      P ⟶ (f.ringSheafPushforward).obj
        ((F.sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology (Y : TopCat))
          (Opens.grothendieckTopology (Z : TopCat))).obj P) :=
    fun P => ⟨Functor.whiskerRight (NatTrans.op adj.counit) P.obj⟩
  have hnatA : ∀ {P Q : Sheaf (Opens.grothendieckTopology (Z : TopCat)) RingCat.{u}} (α : P ⟶ Q),
      α ≫ mkA Q = mkA P ≫ (f.ringSheafPushforward).map
        ((F.sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology (Y : TopCat))
          (Opens.grothendieckTopology (Z : TopCat))).map α) := by
    intro P Q α
    apply Sheaf.hom_ext
    ext W : 2
    exact (α.hom.naturality (adj.counit.app W.unop).op).symm
  have hstructS : mkA Z.ringSheafOnOpens =
      f.ringSheafOnOpensHom ≫ (f.ringSheafPushforward).map σ :=
    Sheaf.hom_ext hstruct
  have hAstage : ∀ n, frobeniusColimitι Z p hZ n ≫ mkA (frobeniusColimitRingSheaf Z p hZ) =
      frobeniusColimitι Z p hZ n ≫ frobeniusColimitStructureSheafHom p f hY hZ ≫
        (f.ringSheafPushforward).map φ.hom := by
    intro n
    rw [hnatA (frobeniusColimitι Z p hZ n), hstructS, Category.assoc, ← Functor.map_comp,
      hk n, Functor.map_comp, ← Category.assoc, ← Category.assoc,
      frobeniusColimitι_comp_frobeniusColimitStructureSheafHom p f hY hZ n]
  have hA : mkA (frobeniusColimitRingSheaf Z p hZ) =
      frobeniusColimitStructureSheafHom p f hY hZ ≫ (f.ringSheafPushforward).map φ.hom :=
    endoColimit_hom_ext (frobeniusRingSheafOnOpensHom Z p hZ) hAstage
  exact _root_.SheafOfModules.pushforwardAdjOfIsIso adj φ.hom _ (Sheaf.hom_ext_iff.mp hA)

end General

/-- **Restriction to an open subscheme is left adjoint to pushforward along the open
immersion**, for the Frobenius colimits of the structure sheaves.

This is `AlgebraicGeometry.frobeniusColimitSiteRestrictAdjunctionOfIso` at the open immersion
`V.ι` and the adjoint pair of continuous site functors `V.ι ''ᵁ - ⊣ V.ι ⁻¹ᵁ -`.  Its two inputs
are discharged at once: the comparison `σ` of the structure sheaves is the **identity**, because
`𝒪_V` *is* the pushforward of `𝒪_X` along the open-image functor, so the presentation of the
comorphism of `V.ι` as the counit holds on sections by `rfl`; and the stage compatibility is
`AlgebraicGeometry.frobeniusColimitι_comp_frobeniusColimitRingSheafRestrictIso_hom`. -/
noncomputable def frobeniusColimitSiteRestrictAdjunction :
    frobeniusColimitSiteRestrict X p hX V hV ⊣
      _root_.SheafOfModules.pushforward.{u}
        (frobeniusColimitStructureSheafHom p V.ι hV hX) := by
  let H : Topology.IsOpenEmbedding (TopCat.Hom.hom V.ι.base) := Scheme.Hom.isOpenEmbedding V.ι
  letI : H.isOpenMap.functor.IsContinuous
      (Opens.grothendieckTopology (V.toScheme : TopCat))
      (Opens.grothendieckTopology (X : TopCat)) := H.functor_isContinuous
  exact frobeniusColimitSiteRestrictAdjunctionOfIso p V.ι hV hX H.isOpenMap.adjunction (𝟙 _)
    (frobeniusColimitRingSheafRestrictIso X p hX V hV).symm
    (by ext W x; rfl)
    (fun n => (Category.id_comp _).trans ((Iso.eq_comp_inv _).mpr
      (frobeniusColimitι_comp_frobeniusColimitRingSheafRestrictIso_hom X p hX V hV n)))

/-- **The transition functor of [Stacks, Tag 0EXE] along an open immersion is restriction to the
open subscheme.** -/
noncomputable def frobeniusColimitSiteRestrictIsoPullback :
    frobeniusColimitSiteRestrict X p hX V hV ≅
      _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p V.ι hV hX) :=
  (frobeniusColimitSiteRestrictAdjunction X p hX V hV).leftAdjointUniq
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} _)

end AlgebraicGeometry

end
