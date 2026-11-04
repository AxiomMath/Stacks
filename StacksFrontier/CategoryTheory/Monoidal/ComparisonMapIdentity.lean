module

public import StacksFrontier.CategoryTheory.Monoidal.ComparisonMapComp

/-!
# The comparison map of an adjunction isomorphic to the identity, and along an open square

For an oplax monoidal `F : C ⥤ C` isomorphic to the identity through a monoidal isomorphism,
with `F ⊣ G` and `G ⊣ a`, the comparison map `F K ⊗ a L ⟶ a (K ⊗ L)` is, through the induced
identifications of `G` and `a` with the identity, the identity of `K ⊗ L`.

Combined with the comparison map of a composite ([Stacks, Tag 0B6R]) and its base change
([Stacks, Tag 0B6P]) this gives the compatibility of comparison maps along a morphism of
compactifications used in the proof of [Stacks, Tag 0B6T].

## Main results

* `CategoryTheory.Adjunction.comparisonMap_comp_eq_of_iso_id`
* `Stacks.CategoryTheory.BaseChange.map_comparisonMap_comp_comp_rightAdjointBaseChange`
* `Stacks.CategoryTheory.BaseChange.comparisonMap_comp_rightAdjointBaseChange_of_iso`
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.Functor.FullyFaithful

variable {C : Type*} [Category C] {P : C ⥤ C} (hP : P.FullyFaithful) (c : P ⋙ P ≅ P)

/-- A fully faithful endofunctor `P` with `P ⋙ P ≅ P` is isomorphic to the identity: the
component at `X` is the preimage under `P` of `c : P (P X) ≅ P X`. -/
def isoIdOfCompIso : P ≅ 𝟭 C :=
  NatIso.ofComponents (fun X => hP.preimageIso (c.app X)) fun {X Y} f => hP.map_injective (by
    simp only [Functor.id_obj, Functor.id_map, FullyFaithful.preimageIso_hom, Functor.map_comp,
      FullyFaithful.map_preimage]
    exact c.hom.naturality f)

/-- The isomorphism `P ≅ 𝟭` of `isoIdOfCompIso` is compatible with the oplax structure when `P`
is monoidal and `c` is a monoidal isomorphism. -/
lemma δ_comp_isoIdOfCompIso [MonoidalCategory C] [P.Monoidal] [NatTrans.IsMonoidal c.hom]
    (K N : C) :
    Functor.OplaxMonoidal.δ P K N ≫
        ((hP.isoIdOfCompIso c).hom.app K ⊗ₘ (hP.isoIdOfCompIso c).hom.app N) =
      (hP.isoIdOfCompIso c).hom.app (K ⊗ N) := by
  apply hP.map_injective
  have e (X : C) : P.map ((hP.isoIdOfCompIso c).hom.app X) = c.hom.app X := hP.map_preimage _
  have h₁ := NatTrans.IsMonoidal.δ_comp_tensorHom c.hom K N
  have h₂ : P.map ((hP.isoIdOfCompIso c).hom.app K ⊗ₘ (hP.isoIdOfCompIso c).hom.app N) ≫
      Functor.OplaxMonoidal.δ P K N =
      Functor.OplaxMonoidal.δ P (P.obj K) (P.obj N) ≫ (c.hom.app K ⊗ₘ c.hom.app N) := by
    have := (Functor.OplaxMonoidal.δ_natural P ((hP.isoIdOfCompIso c).hom.app K)
      ((hP.isoIdOfCompIso c).hom.app N)).symm
    rw [e, e] at this
    exact this
  simp only [Functor.OplaxMonoidal.comp_δ] at h₁
  rw [e, P.map_comp, ← cancel_mono (Functor.OplaxMonoidal.δ P K N),
    Category.assoc, h₂, ← Category.assoc, h₁]

/-- For `adj : F ⊣ G` with `F ≅ 𝟭`, the identification `G ≅ 𝟭` induced by `rightAdjointUniq` is
compatible with the counits. -/
private lemma map_rightAdjointUniq_inv_comp_counit {F G : C ⥤ C} (adj : F ⊣ G) (e : F ≅ 𝟭 C)
    (M : C) :
    F.map ((Adjunction.rightAdjointUniq (adj.ofNatIsoLeft e) Adjunction.id).inv.app M) ≫
        adj.counit.app M =
      e.symm.inv.app ((𝟭 C).obj M) ≫ (Adjunction.id : 𝟭 C ⊣ 𝟭 C).counit.app M := by
  set i := Adjunction.rightAdjointUniq (adj.ofNatIsoLeft e) Adjunction.id
  have h := Adjunction.rightAdjointUniq_hom_app_counit (adj.ofNatIsoLeft e) Adjunction.id M
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Adjunction.id_counit,
    NatTrans.id_app, Functor.id_map] at h
  have h' : i.hom.app M = e.inv.app (G.obj M) ≫ adj.counit.app M := by
    simpa only [Functor.comp_obj, Functor.id_obj, Category.comp_id,
      Functor.whiskerLeft_app] using h
  have h2 : adj.counit.app M = e.hom.app (G.obj M) ≫ i.hom.app M := by
    rw [h', Iso.hom_inv_id_app_assoc]
  simp only [Iso.symm_inv, Adjunction.id_counit, NatTrans.id_app]
  rw [h2, ← Category.assoc, e.hom.naturality]
  simp

end CategoryTheory.Functor.FullyFaithful

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- The projection map of the identity adjunction is the identity. -/
lemma projectionMap_id (K M : C) :
    (Adjunction.id : 𝟭 C ⊣ 𝟭 C).projectionMap K M = 𝟙 _ := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit (Adjunction.id : 𝟭 C ⊣ 𝟭 C)
  rw [map_projectionMap_comp_counit]
  simp

/-- The projection map of the identity adjunction is an isomorphism. -/
instance (K M : C) : IsIso ((Adjunction.id : 𝟭 C ⊣ 𝟭 C).projectionMap K M) := by
  rw [projectionMap_id]; infer_instance

/-- The comparison map of the identity adjunctions is the identity. -/
lemma comparisonMap_id (K L : C) :
    (Adjunction.id : 𝟭 C ⊣ 𝟭 C).comparisonMap Adjunction.id K L = 𝟙 _ := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit (Adjunction.id : 𝟭 C ⊣ 𝟭 C)
  rw [map_comparisonMap_comp_counit]
  simp [projectionMap_id]

variable {F G a : C ⥤ C} (adj : F ⊣ G) (b : G ⊣ a) [F.OplaxMonoidal]
  [∀ K M : C, IsIso (adj.projectionMap K M)] (e : F ≅ 𝟭 C)
  (he : ∀ K N : C, δ F K N ≫ (e.hom.app K ⊗ₘ e.hom.app N) = e.hom.app (K ⊗ N))

include he in
/-- **The comparison map of an adjunction isomorphic to the identity** is the identity: for
`e : F ≅ 𝟭` compatible with the oplax structure, and the identifications of `G` and `a` with the
identity it induces, the comparison map at `(K, L)` followed by `a ≅ 𝟭` is `e ⊗ (a ≅ 𝟭)`. -/
lemma comparisonMap_comp_eq_of_iso_id (K L : C) :
    adj.comparisonMap b K L ≫
        (Adjunction.rightAdjointUniq (b.ofNatIsoLeft
          (Adjunction.rightAdjointUniq (adj.ofNatIsoLeft e) Adjunction.id))
            Adjunction.id).hom.app (K ⊗ L) =
      (e.hom.app K ⊗ₘ (Adjunction.rightAdjointUniq (b.ofNatIsoLeft
          (Adjunction.rightAdjointUniq (adj.ofNatIsoLeft e) Adjunction.id))
            Adjunction.id).hom.app L) := by
  set i := Adjunction.rightAdjointUniq (adj.ofNatIsoLeft e) Adjunction.id
  set j := Adjunction.rightAdjointUniq (b.ofNatIsoLeft i) Adjunction.id
  have hi := Functor.FullyFaithful.map_rightAdjointUniq_inv_comp_counit adj e
  have hj := Functor.FullyFaithful.map_rightAdjointUniq_inv_comp_counit b i
  have he' : ∀ K N : C, δ (𝟭 C) K N ≫ (e.symm.hom.app K ⊗ₘ e.symm.hom.app N) =
      e.symm.hom.app (K ⊗ N) ≫ δ F K N := fun K N => by
    simp only [Iso.symm_hom, Functor.OplaxMonoidal.id_δ, Category.id_comp]
    rw [← cancel_epi (e.hom.app (K ⊗ N)), Iso.hom_inv_id_app_assoc, ← he, Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app,
      MonoidalCategory.id_tensorHom_id]
    simp
  have key := comparisonMap_of_iso (Adjunction.id : 𝟭 C ⊣ 𝟭 C) adj e.symm i.symm he' hi
    (Adjunction.id : 𝟭 C ⊣ 𝟭 C) b j.symm hj K L
  rw [key, comparisonMap_id]
  simp only [Iso.symm_inv, Category.id_comp, Category.assoc, Iso.symm_hom,
    Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id]

end CategoryTheory.Adjunction

namespace Stacks.CategoryTheory

variable {A B C : Type*} [Category A] [Category B] [Category C] [MonoidalCategory A]
  [MonoidalCategory B] [MonoidalCategory C] {F : A ⥤ B} {G : B ⥤ A} {a : A ⥤ B}
  [F.OplaxMonoidal] (adj : F ⊣ G) (b : G ⊣ a) [∀ K M, IsIso (adj.projectionMap K M)]
  (J : B ⥤ C) [J.OplaxMonoidal] [∀ K N : B, IsIso (δ J K N)] {P : A ⥤ C} (κ : F ⋙ J ≅ P)

/-- **The one-variable comparison map read along `J`**: for `F ⊣ G ⊣ a`, a strong `J` and
`κ : F ⋙ J ≅ P`, the map `P K ⊗ J (a U) ⟶ J (a K)` given by `κ⁻¹`, the inverse of the oplax
structure of `J`, and `J` of the comparison map at `(K, U)` followed by `a` of the right unitor.
For `F = Lf̄^*`, `J = Lj^*` along a compactification it is `μ_{f,K}` of [Stacks, Tag 0B6T]. -/
def comparisonMapAlong {U : A} (hU : 𝟙_ A = U) (K : A) :
    P.obj K ⊗ J.obj (a.obj U) ⟶ J.obj (a.obj K) :=
  κ.inv.app K ▷ J.obj (a.obj U) ≫ inv (δ J (F.obj K) (a.obj U)) ≫
    J.map (adj.comparisonMap b K U ≫ a.map (K ◁ eqToHom hU.symm ≫ (ρ_ K).hom))

/-- **`comparisonMapAlong` is natural in `K`.** -/
@[reassoc]
lemma comparisonMapAlong_naturality {U : A} (hU : 𝟙_ A = U) {K K' : A} (h : K ⟶ K') :
    P.map h ▷ J.obj (a.obj U) ≫ comparisonMapAlong adj b J κ hU K' =
      comparisonMapAlong adj b J κ hU K ≫ J.map (a.map h) := by
  subst hU
  have hκ : P.map h ≫ κ.inv.app K' = κ.inv.app K ≫ J.map (F.map h) := (κ.inv.naturality h)
  have hδ : J.map (F.map h) ▷ J.obj (a.obj (𝟙_ A)) ≫ inv (δ J (F.obj K') (a.obj (𝟙_ A))) =
      inv (δ J (F.obj K) (a.obj (𝟙_ A))) ≫ J.map (F.map h ▷ a.obj (𝟙_ A)) := by
    rw [IsIso.comp_inv_eq, Category.assoc, ← Functor.OplaxMonoidal.δ_natural_left,
      IsIso.inv_hom_id_assoc]
  have hc : F.map h ▷ a.obj (𝟙_ A) ≫ adj.comparisonMap b K' (𝟙_ A) ≫
      a.map (K' ◁ eqToHom rfl ≫ (ρ_ K').hom) =
      (adj.comparisonMap b K (𝟙_ A) ≫ a.map (K ◁ eqToHom rfl ≫ (ρ_ K).hom)) ≫ a.map h := by
    rw [Adjunction.comparisonMap_naturality_left_assoc]
    simp only [eqToHom_refl, MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.assoc,
      ← a.map_comp, MonoidalCategory.rightUnitor_naturality]
  simp only [comparisonMapAlong, Category.assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, hκ, MonoidalCategory.comp_whiskerRight_assoc,
    reassoc_of% hδ, ← J.map_comp, hc, J.map_comp]

end Stacks.CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

open Stacks.AffineProjectionFormula

variable {A B₂ B₁ C : Type*} [Category A] [Category B₂] [Category B₁] [Category C]
  [MonoidalCategory A] [MonoidalCategory B₂] [MonoidalCategory B₁] [MonoidalCategory C]
  {F₂ : A ⥤ B₂} {G₂ : B₂ ⥤ A} {a₂ : A ⥤ B₂} {Fg : B₂ ⥤ B₁} {Gg : B₁ ⥤ B₂} {ag : B₂ ⥤ B₁}
  {J₂ : B₂ ⥤ C} {R₂ : C ⥤ B₂} {J₁ : B₁ ⥤ C} {R₁ : C ⥤ B₁}
  {FI : C ⥤ C} {GI : C ⥤ C} {aI : C ⥤ C} {Lc : B₂ ⥤ C}
  [F₂.OplaxMonoidal] [Fg.OplaxMonoidal] [J₂.OplaxMonoidal] [J₁.OplaxMonoidal] [FI.OplaxMonoidal]
  (adj₂ : F₂ ⊣ G₂) (b₂ : G₂ ⊣ a₂) (adjg : Fg ⊣ Gg) (bg : Gg ⊣ ag)
  (adjJ₂ : J₂ ⊣ R₂) (adjJ₁ : J₁ ⊣ R₁) (adjI : FI ⊣ GI) (bI : GI ⊣ aI)
  [∀ K M, IsIso (adj₂.projectionMap K M)] [∀ K M, IsIso (adjg.projectionMap K M)]
  [∀ K M, IsIso (adjI.projectionMap K M)]
  (eg : J₂ ⋙ FI ≅ Lc) (ef : Fg ⋙ J₁ ≅ Lc)
  (hsq : ∀ K N : B₂, FI.map (δ J₂ K N) ≫ δ FI (J₂.obj K) (J₂.obj N) ≫
      ((squareCompositeIso eg ef).hom.app K ⊗ₘ (squareCompositeIso eg ef).hom.app N) =
    (squareCompositeIso eg ef).hom.app (K ⊗ N) ≫ J₁.map (δ Fg K N) ≫
      δ J₁ (Fg.obj K) (Fg.obj N))
  [IsIso (twoSquare adjg adjI eg ef).natTrans]
  (e : FI ≅ 𝟭 C)
  (he : ∀ K N : C, δ FI K N ≫ (e.hom.app K ⊗ₘ e.hom.app N) = e.hom.app (K ⊗ N))
  [∀ K N : B₂, IsIso (δ J₂ K N)]

include hsq he in
/-- **The comparison map along a morphism of compactifications.** In an open square where the
base change `FI` of `Fg` is isomorphic to the identity, `J₁` of the comparison map of the
composite `F₂ ⋙ Fg` at `(K, L)`, followed by the base change map `α` and the identification of
`aI` with the identity, is `J₁ (F₂ K) ⊗ J₁ (a₂ L)` carried to `J₂ (F₂ K) ⊗ J₂ (a₂ L)` by the
identification of the composites around the square and by `α`, then `J₂` of the comparison map
of `F₂` at `(K, L)`. This is the commutative diagram of the proof of [Stacks, Tag 0B6T]
comparing the maps `μ` of two compactifications. -/
theorem map_comparisonMap_comp_comp_rightAdjointBaseChange (K L : A) :
    J₁.map ((adj₂.comp adjg).comparisonMap (bg.comp b₂) K L) ≫
        (rightAdjointBaseChange adjg adjI adjJ₂ adjJ₁ eg ef bg bI).natTrans.app (a₂.obj (K ⊗ L)) ≫
          (Adjunction.rightAdjointUniq (bI.ofNatIsoLeft
            (Adjunction.rightAdjointUniq (adjI.ofNatIsoLeft e) Adjunction.id))
              Adjunction.id).hom.app (J₂.obj (a₂.obj (K ⊗ L))) =
      δ J₁ (Fg.obj (F₂.obj K)) (ag.obj (a₂.obj L)) ≫
        (((squareCompositeIso eg ef).inv.app (F₂.obj K) ≫ e.hom.app _) ⊗ₘ
          ((rightAdjointBaseChange adjg adjI adjJ₂ adjJ₁ eg ef bg bI).natTrans.app (a₂.obj L) ≫
            (Adjunction.rightAdjointUniq (bI.ofNatIsoLeft
              (Adjunction.rightAdjointUniq (adjI.ofNatIsoLeft e) Adjunction.id))
                Adjunction.id).hom.app (J₂.obj (a₂.obj L)))) ≫
        inv (δ J₂ (F₂.obj K) (a₂.obj L)) ≫ J₂.map (adj₂.comparisonMap b₂ K L) := by
  set α := rightAdjointBaseChange adjg adjI adjJ₂ adjJ₁ eg ef bg bI
  set j := Adjunction.rightAdjointUniq (bI.ofNatIsoLeft
    (Adjunction.rightAdjointUniq (adjI.ofNatIsoLeft e) Adjunction.id)) Adjunction.id
  have hc := Adjunction.comparisonMap_comp adj₂ adjg b₂ bg K L
  have hn : J₁.map (ag.map (adj₂.comparisonMap b₂ K L)) ≫ α.natTrans.app (a₂.obj (K ⊗ L)) =
      α.natTrans.app (F₂.obj K ⊗ a₂.obj L) ≫ aI.map (J₂.map (adj₂.comparisonMap b₂ K L)) :=
    α.natTrans.naturality _
  have hb := comparisonMap_baseChange adjg adjI adjJ₂ adjJ₁ eg ef hsq bg bI (F₂.obj K) (a₂.obj L)
  have hb' : J₁.map (adjg.comparisonMap bg (F₂.obj K) (a₂.obj L)) ≫
      α.natTrans.app (F₂.obj K ⊗ a₂.obj L) =
      δ J₁ (Fg.obj (F₂.obj K)) (ag.obj (a₂.obj L)) ≫
        ((squareCompositeIso eg ef).inv.app (F₂.obj K) ⊗ₘ α.natTrans.app (a₂.obj L)) ≫
          adjI.comparisonMap bI (J₂.obj (F₂.obj K)) (J₂.obj (a₂.obj L)) ≫
            aI.map (inv (δ J₂ (F₂.obj K) (a₂.obj L))) := by
    rw [← cancel_mono (aI.map (δ J₂ (F₂.obj K) (a₂.obj L)))]
    simp only [Category.assoc, ← aI.map_comp, IsIso.inv_hom_id, aI.map_id, Category.comp_id]
    exact hb
  have hI := Adjunction.comparisonMap_comp_eq_of_iso_id adjI bI e he
    (J₂.obj (F₂.obj K)) (J₂.obj (a₂.obj L))
  have nj₁ : aI.map (inv (δ J₂ (F₂.obj K) (a₂.obj L))) ≫
      aI.map (J₂.map (adj₂.comparisonMap b₂ K L)) ≫ j.hom.app (J₂.obj (a₂.obj (K ⊗ L))) =
      j.hom.app _ ≫ inv (δ J₂ (F₂.obj K) (a₂.obj L)) ≫ J₂.map (adj₂.comparisonMap b₂ K L) := by
    rw [← aI.map_comp_assoc]
    exact j.hom.naturality _
  rw [hc, J₁.map_comp, Category.assoc, reassoc_of% hn, reassoc_of% hb', nj₁, reassoc_of% hI,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc]

variable {F₁ : A ⥤ B₁} {G₁ : B₁ ⥤ A} {a₁ : A ⥤ B₁} [F₁.OplaxMonoidal] (adj₁ : F₁ ⊣ G₁)
  (b₁ : G₁ ⊣ a₁) [∀ K M, IsIso (adj₁.projectionMap K M)] [∀ K N : B₁, IsIso (δ J₁ K N)]
  (e₁ : F₂ ⋙ Fg ≅ F₁) (i₁ : Gg ⋙ G₂ ≅ G₁) (θ : a₁ ≅ a₂ ⋙ ag)
  (he₁ : ∀ K N : A, δ (F₂ ⋙ Fg) K N ≫ (e₁.hom.app K ⊗ₘ e₁.hom.app N) =
    e₁.hom.app (K ⊗ N) ≫ δ F₁ K N)
  (hi₁ : ∀ M : B₁, F₁.map (i₁.hom.app M) ≫ adj₁.counit.app M =
    e₁.inv.app ((Gg ⋙ G₂).obj M) ≫ (adj₂.comp adjg).counit.app M)
  (hθ : ∀ L : A, G₁.map (θ.inv.app L) ≫ b₁.counit.app L =
    i₁.inv.app ((a₂ ⋙ ag).obj L) ≫ (bg.comp b₂).counit.app L)
  {P : A ⥤ C} (κ₁ : F₁ ⋙ J₁ ≅ P) (κ₂ : F₂ ⋙ J₂ ≅ P)
  (hκ : ∀ K : A, κ₁.inv.app K ≫ J₁.map (e₁.inv.app K) ≫ (squareCompositeIso eg ef).inv.app
    (F₂.obj K) ≫ e.hom.app _ = κ₂.inv.app K)

include hsq he he₁ hi₁ hθ hκ in
/-- **The comparison maps along a morphism of compactifications, in two variables.** With
`α Z : J₁ (a₁ Z) ⟶ J₂ (a₂ Z)` the composite of `J₁` of `a₁ ≅ a₂ ⋙ ag`, the base change map and the
identification of `aI` with the identity, the map `P K ⊗ J₁ (a₁ L) ⟶ J₁ (a₁ (K ⊗ L))` given by
`κ₁⁻¹`, the inverse of the oplax structure of `J₁` and `J₁` of the comparison map of
`F₁ ⊣ G₁ ⊣ a₁`, followed by `α (K ⊗ L)`, is `P K ◁ α L` followed by the same map for
`F₂ ⊣ G₂ ⊣ a₂` along `J₂`. This is the commutative diagram of the proof of [Stacks, Tag 0B6T],
in both variables. -/
theorem comparisonMap_comp_rightAdjointBaseChange_of_iso (K L : A) :
    κ₁.inv.app K ▷ J₁.obj (a₁.obj L) ≫ inv (δ J₁ (F₁.obj K) (a₁.obj L)) ≫
        J₁.map (adj₁.comparisonMap b₁ K L) ≫
        (J₁.map (θ.hom.app (K ⊗ L)) ≫
          (rightAdjointBaseChange adjg adjI adjJ₂ adjJ₁ eg ef bg bI).natTrans.app (a₂.obj (K ⊗ L)) ≫
          (Adjunction.rightAdjointUniq (bI.ofNatIsoLeft
            (Adjunction.rightAdjointUniq (adjI.ofNatIsoLeft e) Adjunction.id))
              Adjunction.id).hom.app (J₂.obj (a₂.obj (K ⊗ L)))) =
      P.obj K ◁ (J₁.map (θ.hom.app L) ≫
          (rightAdjointBaseChange adjg adjI adjJ₂ adjJ₁ eg ef bg bI).natTrans.app (a₂.obj L) ≫
          (Adjunction.rightAdjointUniq (bI.ofNatIsoLeft
            (Adjunction.rightAdjointUniq (adjI.ofNatIsoLeft e) Adjunction.id))
              Adjunction.id).hom.app (J₂.obj (a₂.obj L))) ≫
        κ₂.inv.app K ▷ J₂.obj (a₂.obj L) ≫ inv (δ J₂ (F₂.obj K) (a₂.obj L)) ≫
        J₂.map (adj₂.comparisonMap b₂ K L) := by
  set α := rightAdjointBaseChange adjg adjI adjJ₂ adjJ₁ eg ef bg bI
  set j := Adjunction.rightAdjointUniq (bI.ofNatIsoLeft
    (Adjunction.rightAdjointUniq (adjI.ofNatIsoLeft e) Adjunction.id)) Adjunction.id
  have core := map_comparisonMap_comp_comp_rightAdjointBaseChange adj₂ b₂ adjg bg adjJ₂ adjJ₁
    adjI bI eg ef hsq e he K L
  have hcmp := Adjunction.comparisonMap_of_iso (adj₂.comp adjg) adj₁ e₁ i₁ he₁ hi₁
    (bg.comp b₂) b₁ θ.symm hθ K L
  have s₄ : adj₁.comparisonMap b₁ K L ≫ θ.hom.app (K ⊗ L) =
      (e₁.inv.app K ⊗ₘ θ.hom.app L) ≫ (adj₂.comp adjg).comparisonMap (bg.comp b₂) K L := by
    rw [hcmp]; simp
  have s₆ : inv (δ J₁ (F₁.obj K) (a₁.obj L)) ≫ J₁.map (e₁.inv.app K ⊗ₘ θ.hom.app L) ≫
      δ J₁ (Fg.obj (F₂.obj K)) (ag.obj (a₂.obj L)) =
      (J₁.map (e₁.inv.app K) ⊗ₘ J₁.map (θ.hom.app L)) := by
    rw [IsIso.inv_comp_eq, Functor.OplaxMonoidal.δ_natural]; rfl
  have s₇ : κ₁.inv.app K ▷ J₁.obj (a₁.obj L) ≫
      (J₁.map (e₁.inv.app K) ⊗ₘ J₁.map (θ.hom.app L)) ≫
      (((squareCompositeIso eg ef).inv.app (F₂.obj K) ≫ e.hom.app _) ⊗ₘ
        (α.natTrans.app (a₂.obj L) ≫ j.hom.app (J₂.obj (a₂.obj L)))) =
      P.obj K ◁ (J₁.map (θ.hom.app L) ≫ α.natTrans.app (a₂.obj L) ≫
        j.hom.app (J₂.obj (a₂.obj L))) ≫ κ₂.inv.app K ▷ J₂.obj (a₂.obj L) := by
    rw [← hκ K]
    simp only [← MonoidalCategory.id_tensorHom, ← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.assoc]
    exact congrArg _ (by simp)
  have L' : J₁.map (adj₁.comparisonMap b₁ K L) ≫ J₁.map (θ.hom.app (K ⊗ L)) ≫
      α.natTrans.app (a₂.obj (K ⊗ L)) ≫ j.hom.app (J₂.obj (a₂.obj (K ⊗ L))) =
      J₁.map (e₁.inv.app K ⊗ₘ θ.hom.app L) ≫ δ J₁ (Fg.obj (F₂.obj K)) (ag.obj (a₂.obj L)) ≫
        (((squareCompositeIso eg ef).inv.app (F₂.obj K) ≫ e.hom.app _) ⊗ₘ
          (α.natTrans.app (a₂.obj L) ≫ j.hom.app (J₂.obj (a₂.obj L)))) ≫
        inv (δ J₂ (F₂.obj K) (a₂.obj L)) ≫ J₂.map (adj₂.comparisonMap b₂ K L) := by
    rw [← J₁.map_comp_assoc, s₄, J₁.map_comp, Category.assoc, core]
  rw [L', reassoc_of% s₆, reassoc_of% s₇]

include hsq he he₁ hi₁ hθ hκ in
/-- **The restricted one-variable comparison maps along a morphism of compactifications.** With
`μᵢ K : P K ⊗ Jᵢ (aᵢ U) ⟶ Jᵢ (aᵢ K)` the map `Stacks.CategoryTheory.comparisonMapAlong` of
`Fᵢ ⊣ Gᵢ ⊣ aᵢ` along `Jᵢ`, and `α K : J₁ (a₁ K) ⟶ J₂ (a₂ K)` the composite of `J₁` of
`a₁ ≅ a₂ ⋙ ag`, the base change map and the identification of `aI` with the identity, one has
`μ₁ K ≫ α K = (P K ◁ α U) ≫ μ₂ K`. This is the independence of `μ_{f,K}` of the
compactification in the proof of [Stacks, Tag 0B6T]. -/
theorem comparisonMapAlong_comp_rightAdjointBaseChange {U : A} (hU : 𝟙_ A = U) (K : A) :
    comparisonMapAlong adj₁ b₁ J₁ κ₁ hU K ≫
        (J₁.map (θ.hom.app K) ≫
          (rightAdjointBaseChange adjg adjI adjJ₂ adjJ₁ eg ef bg bI).natTrans.app (a₂.obj K) ≫
          (Adjunction.rightAdjointUniq (bI.ofNatIsoLeft
            (Adjunction.rightAdjointUniq (adjI.ofNatIsoLeft e) Adjunction.id))
              Adjunction.id).hom.app (J₂.obj (a₂.obj K))) =
      P.obj K ◁ (J₁.map (θ.hom.app U) ≫
          (rightAdjointBaseChange adjg adjI adjJ₂ adjJ₁ eg ef bg bI).natTrans.app (a₂.obj U) ≫
          (Adjunction.rightAdjointUniq (bI.ofNatIsoLeft
            (Adjunction.rightAdjointUniq (adjI.ofNatIsoLeft e) Adjunction.id))
              Adjunction.id).hom.app (J₂.obj (a₂.obj U))) ≫
        comparisonMapAlong adj₂ b₂ J₂ κ₂ hU K := by
  set α := rightAdjointBaseChange adjg adjI adjJ₂ adjJ₁ eg ef bg bI
  set j := Adjunction.rightAdjointUniq (bI.ofNatIsoLeft
    (Adjunction.rightAdjointUniq (adjI.ofNatIsoLeft e) Adjunction.id)) Adjunction.id
  set ρ' : K ⊗ U ⟶ K := K ◁ eqToHom hU.symm ≫ (ρ_ K).hom
  have two := comparisonMap_comp_rightAdjointBaseChange_of_iso adj₂ b₂ adjg bg adjJ₂ adjJ₁
    adjI bI eg ef hsq e he adj₁ b₁ e₁ i₁ θ he₁ hi₁ hθ κ₁ κ₂ hκ K U
  have s₁ : a₁.map ρ' ≫ θ.hom.app K = θ.hom.app (K ⊗ U) ≫ ag.map (a₂.map ρ') :=
    θ.hom.naturality ρ'
  have s₂ : J₁.map (ag.map (a₂.map ρ')) ≫ α.natTrans.app (a₂.obj K) =
      α.natTrans.app (a₂.obj (K ⊗ U)) ≫ aI.map (J₂.map (a₂.map ρ')) :=
    α.natTrans.naturality _
  have s₃ : aI.map (J₂.map (a₂.map ρ')) ≫ j.hom.app (J₂.obj (a₂.obj K)) =
      j.hom.app (J₂.obj (a₂.obj (K ⊗ U))) ≫ J₂.map (a₂.map ρ') :=
    j.hom.naturality _
  have n : J₁.map (a₁.map ρ') ≫ J₁.map (θ.hom.app K) ≫ α.natTrans.app (a₂.obj K) ≫
      j.hom.app (J₂.obj (a₂.obj K)) =
      (J₁.map (θ.hom.app (K ⊗ U)) ≫ α.natTrans.app (a₂.obj (K ⊗ U)) ≫
        j.hom.app (J₂.obj (a₂.obj (K ⊗ U)))) ≫ J₂.map (a₂.map ρ') := by
    rw [← J₁.map_comp_assoc, s₁, J₁.map_comp, Category.assoc, reassoc_of% s₂, s₃]
    simp only [Category.assoc]
  simp only [comparisonMapAlong, Category.assoc]
  rw [J₁.map_comp, Category.assoc, n]
  simp only [Category.assoc] at two ⊢
  rw [reassoc_of% two, J₂.map_comp]

end Stacks.CategoryTheory.BaseChange
