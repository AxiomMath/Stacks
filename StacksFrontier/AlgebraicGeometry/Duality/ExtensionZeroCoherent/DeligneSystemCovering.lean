module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.EssentiallyConstantCover
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionLiftingCover

/-!
# Being pro-isomorphic to a Deligne system is local on `X`

Let `j : U → X` be an open immersion of Noetherian schemes and let `(K_n)` be an inverse system
in `D^b_{Coh}(𝒪_X)`. [Stacks, Tag 0G4T] says that, for a finite open covering
`X = W_1 ∪ … ∪ W_r`, the system `(K_n)` is pro-isomorphic to a Deligne system if and only if each
restriction `(K_n|_{W_i})` is pro-isomorphic to a Deligne system with respect to the open
immersion `U ∩ W_i → W_i`.

The proof is the source's. One direction is that Deligne systems restrict to Deligne systems,
`AlgebraicGeometry.ProIsoDeligneSystem.restrict`. For the other, an induction on `r` reduces to a
covering `X = V ∪ W` by two opens. A system pro-isomorphic to a Deligne system is characterized by
two properties of the restriction to `U`
(`AlgebraicGeometry.proIsoDeligneSystem_iff_isEssentiallyConstantPro_and_restrictionLifting`):
`(K_n|_U)` is essentially constant, and restriction identifies `colim_n Hom_X(K_n, L)` with
`colim_n Hom_U(K_n|_U, L|_U)` for every `L` (Stacks 0G2H and 0G2X). Both properties are local:
the first by the Mayer–Vietoris triangle of Stacks 08BU and Stacks 0G3A
(`AlgebraicGeometry.isEssentiallyConstantPro_of_cover`), the second by the Mayer–Vietoris triangle
of Stacks 08BV and the five lemma (`AlgebraicGeometry.restrictionLifting_of_cover`).

## Main results

* `AlgebraicGeometry.proIsoDeligneSystem_iff_isEssentiallyConstantPro_and_restrictionLifting`:
  the characterization above.
* `AlgebraicGeometry.ProIsoDeligneSystem.congr_range`: being pro-isomorphic to a Deligne system
  depends on the open immersion only through its image.
* `AlgebraicGeometry.proIsoDeligneSystem_of_sup_eq_top`: the case of a covering by two opens.
* `AlgebraicGeometry.proIsoDeligneSystem_iff_forall_restrict`: **[Stacks, Tag 0G4T]**.

## References

* [Stacks Project, Tag 0G4T](https://stacks.math.columbia.edu/tag/0G4T)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 0G4L](https://stacks.math.columbia.edu/tag/0G4L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

attribute [local instance] isNoetherian_opens_toScheme

/-! ### Preliminaries -/

/-- The image of the restriction `f ∣_ W : f⁻¹(W) ⟶ W` of a morphism of schemes to an open `W` of
its target is the preimage in `W` of the image of `f`. -/
public lemma range_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens) :
    Set.range (f ∣_ W).base = W.ι.base ⁻¹' Set.range f.base := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, (morphismRestrict_base_coe f W y).symm⟩
  · rintro ⟨z, hz⟩
    have hzW : z ∈ f ⁻¹ᵁ W := by
      change f.base z ∈ (W : Set Y)
      rw [hz]
      exact x.2
    exact ⟨⟨z, hzW⟩, Subtype.ext ((morphismRestrict_base_coe f W ⟨z, hzW⟩).trans hz)⟩

/-- Evaluating a composite of morphisms of schemes at a point. -/
public lemma apply_eq_of_comp_eq {A B C : Scheme.{u}} {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ C}
    (e : f ≫ g = h) (x : A) : g.base (f.base x) = h.base x := by
  subst e
  rfl

/-- Restricting along two sides of a commutative square of open immersions gives isomorphic
functors on `D^b_{Coh}`. -/
public def restrictBoundedCoherentLiftSquareIso {P Q R Z : Scheme.{u}} [IsLocallyNoetherian Q]
    [IsLocallyNoetherian R] [IsLocallyNoetherian Z] (a : P ⟶ Q) (b : Q ⟶ Z) (c : P ⟶ R)
    (d : R ⟶ Z) [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c] [IsOpenImmersion d]
    (h : a ≫ b = c ≫ d) :
    restrictBoundedCoherentLift b ⋙ restrictBoundedCoherentLift a ≅
      restrictBoundedCoherentLift d ⋙ restrictBoundedCoherentLift c :=
  (restrictBoundedCoherentLiftCompIso a b (a ≫ b) rfl).symm ≪≫
    restrictBoundedCoherentLiftCompIso c d (a ≫ b) h.symm

/-- On a scheme with no points there is exactly one morphism between two sheaves of modules: the
ring of sections over any open is the zero ring, so every module of sections is zero. -/
public lemma subsingleton_hom_modules_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] (M N : Y.Modules) :
    Subsingleton (M ⟶ N) := by
  refine ⟨fun a b => Scheme.Modules.hom_ext _ _ fun V => ?_⟩
  ext x
  exact (Module.subsingleton Γ(Y, V) _).elim _ _

/-- On a scheme with no points every object of the derived category of modules is zero. -/
public lemma isZero_derivedCategory_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y]
    (K : DerivedCategory Y.Modules) : IsZero K := by
  have hC : IsZero (DerivedCategory.Q.objPreimage K) := by
    rw [IsZero.iff_id_eq_zero]
    ext n : 1
    exact (subsingleton_hom_modules_of_isEmpty _ _).elim _ _
  exact (DerivedCategory.Q.map_isZero hC).of_iso (DerivedCategory.Q.objObjPreimageIso K).symm

/-- On a scheme with no points there is at most one morphism between two objects of
`D^b_{Coh}`. -/
public lemma subsingleton_hom_boundedCoherentDerived_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y]
    (A B : BoundedCoherentDerived Y) : Subsingleton (A ⟶ B) :=
  ⟨fun _f _g => (boundedCoherentDerived Y).ι.map_injective
    ((isZero_derivedCategory_of_isEmpty A.obj).eq_of_src _ _)⟩

variable {U X : Scheme.{u}}

/-! ### Being pro-isomorphic to a Deligne system -/

section Characterization

variable {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X]

/-- A system pro-isomorphic to a Deligne system restricts to an essentially constant system on
`U`. -/
public lemma ProIsoDeligneSystem.isEssentiallyConstantPro {F : ℕᵒᵖ ⥤ BoundedCoherentDerived X}
    (h : ProIsoDeligneSystem j F) :
    EssentiallyConstantPro.IsEssentiallyConstantPro (F ⋙ restrictBoundedCoherentLift j) :=
  (DeligneSystem.values j).isEssentiallyConstantPro_of_proIsoDeligne
    (proIsoDeligneSystem_iff.mp h)

/-- For a system pro-isomorphic to a Deligne system, restriction to `U` identifies
`colim_n Hom_X(K_n, L)` with `colim_n Hom_U(K_n|_U, L|_U)`, elementwise. -/
public lemma ProIsoDeligneSystem.restrictionLifting {F : ℕᵒᵖ ⥤ BoundedCoherentDerived X}
    (h : ProIsoDeligneSystem j F) (N : BoundedCoherentDerived X) :
    RestrictionLifting F (restrictBoundedCoherentLift j) N :=
  (DeligneSystem.values j).restrictionLifting_of_proIsoDeligne (proIsoDeligneSystem_iff.mp h) N

/-- **A characterization of the systems pro-isomorphic to a Deligne system.** An inverse system
`(K_n)` in `D^b_{Coh}(𝒪_X)` is pro-isomorphic to a Deligne system along `j` if and only if
`(K_n|_U)` is essentially constant and restriction to `U` identifies `colim_n Hom_X(K_n, L)` with
`colim_n Hom_U(K_n|_U, L|_U)` for every `L`. Given the two conditions, the Deligne system with
the value of `(K_n|_U)` (Stacks 0G4L) has the same functor of points by Stacks 0G2H, which is
the argument of the source. -/
public theorem proIsoDeligneSystem_iff_isEssentiallyConstantPro_and_restrictionLifting
    {F : ℕᵒᵖ ⥤ BoundedCoherentDerived X} :
    ProIsoDeligneSystem j F ↔
      EssentiallyConstantPro.IsEssentiallyConstantPro (F ⋙ restrictBoundedCoherentLift j) ∧
        ∀ N, RestrictionLifting F (restrictBoundedCoherentLift j) N := by
  refine ⟨fun h => ⟨h.isEssentiallyConstantPro, h.restrictionLifting⟩, fun ⟨hess, hRL⟩ => ?_⟩
  rw [proIsoDeligneSystem_iff]
  obtain ⟨c, i, s, hs⟩ := hess
  exact ⟨c.pt, ⟨ProSeq.isoOfSeqHomColimIso
    (proHomComparisonIso F (restrictBoundedCoherentLift j) c i s hs hRL ≪≫
      ((DeligneSystem.values j).systemHomIso c.pt).symm)⟩⟩

/-- On a scheme with no points every inverse system is pro-isomorphic to a Deligne system. -/
public lemma proIsoDeligneSystem_of_isEmpty [IsEmpty X] (F : ℕᵒᵖ ⥤ BoundedCoherentDerived X) :
    ProIsoDeligneSystem j F := by
  have : IsEmpty U := Function.isEmpty j.base
  refine proIsoDeligneSystem_iff_isEssentiallyConstantPro_and_restrictionLifting.mpr
    ⟨⟨⟨(F ⋙ restrictBoundedCoherentLift j).obj (op 0),
      { app := fun _ => 0
        naturality := fun _ _ _ =>
          (subsingleton_hom_boundedCoherentDerived_of_isEmpty _ _).elim _ _ }⟩, op 0, 𝟙 _,
      ⟨(subsingleton_hom_boundedCoherentDerived_of_isEmpty _ _).elim _ _, fun k =>
        ⟨k, (homOfLE (Nat.zero_le k.unop)).op, 𝟙 k,
          (subsingleton_hom_boundedCoherentDerived_of_isEmpty _ _).elim _ _⟩⟩⟩,
      fun N => ⟨fun n _ => ⟨n, le_rfl, 0,
        (subsingleton_hom_boundedCoherentDerived_of_isEmpty _ _).elim _ _⟩,
      fun n _ _ _ => ⟨n, le_rfl,
        (subsingleton_hom_boundedCoherentDerived_of_isEmpty _ _).elim _ _⟩⟩⟩

end Characterization

/-- A Deligne system along `j₁` is a Deligne system along any open immersion `j₂` with the same
image: the image of `j` enters only through the vanishing locus of the ideal. -/
public def DeligneSystem.congrRange {U₁ U₂ : Scheme.{u}} {j₁ : U₁ ⟶ X} {j₂ : U₂ ⟶ X}
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsNoetherian X]
    (h : Set.range j₁.base = Set.range j₂.base) (D : DeligneSystem j₁) : DeligneSystem j₂ :=
  { D with support_idealSheaf := D.support_idealSheaf.trans (by rw [h]) }

/-- **Being pro-isomorphic to a Deligne system depends on the open immersion only through its
image.** -/
public lemma ProIsoDeligneSystem.congr_range {U₁ U₂ : Scheme.{u}} {j₁ : U₁ ⟶ X} {j₂ : U₂ ⟶ X}
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsNoetherian X]
    (h : Set.range j₁.base = Set.range j₂.base) {F : ℕᵒᵖ ⥤ BoundedCoherentDerived X} :
    ProIsoDeligneSystem j₁ F ↔ ProIsoDeligneSystem j₂ F :=
  ⟨fun ⟨D, i⟩ => ⟨D.congrRange h, i⟩, fun ⟨D, i⟩ => ⟨D.congrRange h.symm, i⟩⟩

/-! ### A covering by two opens -/

/-- Restricting a system along an open immersion `f` and then to `f⁻¹(O)` is isomorphic to
restricting it to `O` and then along `f ∣_ O`. -/
private def restrictCompRestrictIso {Y X : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : Y ⟶ X) [IsOpenImmersion f] (O : X.Opens) (F : ℕᵒᵖ ⥤ BoundedCoherentDerived X) :
    (F ⋙ restrictBoundedCoherentLift f) ⋙ restrictBoundedCoherentLift (f ⁻¹ᵁ O).ι ≅
      (F ⋙ restrictBoundedCoherentLift O.ι) ⋙ restrictBoundedCoherentLift (f ∣_ O) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F
    (restrictBoundedCoherentLiftSquareIso _ _ _ _ (morphismRestrict_ι f O).symm) ≪≫
    (Functor.associator _ _ _).symm

/-- **[Stacks, Tag 0G4T] for a covering by two opens**, with `j` the inclusion of an open
subscheme `U`. If `X = V ∪ W` and the restrictions of `(K_n)` to `V` and to `W` are pro-isomorphic
to Deligne systems along `U ∩ V → V` and `U ∩ W → W`, then `(K_n)` is pro-isomorphic to a Deligne
system along `U → X`. -/
public theorem proIsoDeligneSystem_of_sup_eq_top [IsNoetherian X] (U V W : X.Opens)
    (hVW : V ⊔ W = ⊤) (F : ℕᵒᵖ ⥤ BoundedCoherentDerived X)
    (hV : ProIsoDeligneSystem (U.ι ∣_ V) (F ⋙ restrictBoundedCoherentLift V.ι))
    (hW : ProIsoDeligneSystem (U.ι ∣_ W) (F ⋙ restrictBoundedCoherentLift W.ι)) :
    ProIsoDeligneSystem U.ι F := by
  have hVW' : ProIsoDeligneSystem (U.ι ∣_ (V ⊓ W)) (F ⋙ restrictBoundedCoherentLift (V ⊓ W).ι) :=
    ProIsoDeligneSystem.of_natIso
      (Functor.isoWhiskerLeft F
          (restrictBoundedCoherentLiftCompIso _ _ _ (X.homOfLE_ι inf_le_left)) ≪≫
        (Functor.associator _ _ _).symm)
      (hV.restrict (X.homOfLE inf_le_left) (U.ι ∣_ (V ⊓ W)) (by
        rw [range_morphismRestrict, range_morphismRestrict, ← X.homOfLE_ι inf_le_left]
        rfl))
  have ess (O : X.Opens)
      (hO : ProIsoDeligneSystem (U.ι ∣_ O) (F ⋙ restrictBoundedCoherentLift O.ι)) :
      EssentiallyConstantPro.IsEssentiallyConstantPro
        ((F ⋙ restrictBoundedCoherentLift U.ι) ⋙ restrictBoundedCoherentLift (U.ι ⁻¹ᵁ O).ι) :=
    hO.isEssentiallyConstantPro.of_iso (restrictCompRestrictIso U.ι O F).symm
  refine proIsoDeligneSystem_iff_isEssentiallyConstantPro_and_restrictionLifting.mpr
    ⟨isEssentiallyConstantPro_of_cover (U.ι ⁻¹ᵁ V) (U.ι ⁻¹ᵁ W) ?_ _ (ess V hV) (ess W hW)
      (ess (V ⊓ W) hVW'), restrictionLifting_of_cover U V W hVW F hV.restrictionLifting
        hW.restrictionLifting hVW'.restrictionLifting⟩
  change U.ι ⁻¹ᵁ (V ⊔ W) = ⊤
  rw [hVW]
  rfl

/-! ### Finite coverings -/

/-- **The inductive step**: if the restrictions of `(K_n)` to two opens `A` and `B` of `X` are
pro-isomorphic to Deligne systems, so is its restriction to `A ∪ B`. -/
public theorem proIsoDeligneSystem_sup [IsNoetherian X] (U A B : X.Opens)
    (F : ℕᵒᵖ ⥤ BoundedCoherentDerived X)
    (hA : ProIsoDeligneSystem (U.ι ∣_ A) (F ⋙ restrictBoundedCoherentLift A.ι))
    (hB : ProIsoDeligneSystem (U.ι ∣_ B) (F ⋙ restrictBoundedCoherentLift B.ι)) :
    ProIsoDeligneSystem (U.ι ∣_ (A ⊔ B)) (F ⋙ restrictBoundedCoherentLift (A ⊔ B).ι) := by
  set T := A ⊔ B
  let U' : T.toScheme.Opens := T.ι ⁻¹ᵁ U
  have step (O : X.Opens)
      (hO : ProIsoDeligneSystem (U.ι ∣_ O) (F ⋙ restrictBoundedCoherentLift O.ι)) :
      ProIsoDeligneSystem (U'.ι ∣_ (T.ι ⁻¹ᵁ O))
        ((F ⋙ restrictBoundedCoherentLift T.ι) ⋙ restrictBoundedCoherentLift (T.ι ⁻¹ᵁ O).ι) := by
    refine ProIsoDeligneSystem.of_natIso (restrictCompRestrictIso T.ι O F)
      (hO.restrict (T.ι ∣_ O) (U'.ι ∣_ (T.ι ⁻¹ᵁ O)) ?_)
    rw [range_morphismRestrict, range_morphismRestrict, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι]
    ext x
    change T.ι.base ((T.ι ⁻¹ᵁ O).ι.base x) ∈ (U : Set X) ↔
      O.ι.base ((T.ι ∣_ O).base x) ∈ (U : Set X)
    rw [apply_eq_of_comp_eq (morphismRestrict_ι T.ι O),
      apply_eq_of_comp_eq (morphismRestrict_ι T.ι O).symm, morphismRestrict_ι]
  have hcover : T.ι ⁻¹ᵁ A ⊔ T.ι ⁻¹ᵁ B = ⊤ := T.ι_preimage_self
  refine (ProIsoDeligneSystem.congr_range ?_).mp
    (proIsoDeligneSystem_of_sup_eq_top U' (T.ι ⁻¹ᵁ A) (T.ι ⁻¹ᵁ B) hcover
      (F ⋙ restrictBoundedCoherentLift T.ι) (step A hA) (step B hB))
  rw [range_morphismRestrict, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  rfl

/-- **Stacks Project, Tag 0G4T.** Let `j : U → X` be an open immersion of Noetherian schemes, let
`(K_n)` be an inverse system in `D^b_{Coh}(𝒪_X)` and let `X = W_1 ∪ … ∪ W_r` be a finite open
covering. Then `(K_n)` is pro-isomorphic to a Deligne system if and only if, for each `i`, the
restriction `(K_n|_{W_i})` is pro-isomorphic to a Deligne system with respect to the open
immersion `U ∩ W_i → W_i`.

The covering is any family `W : ι → X.Opens` indexed by a finite type, with `⨆ i, W i = ⊤`; the
open immersion `U ∩ W_i → W_i` is the restriction `j ∣_ W i` of `j`. -/
@[stacks 0G4T]
public theorem proIsoDeligneSystem_iff_forall_restrict (j : U ⟶ X) [IsOpenImmersion j]
    [IsNoetherian X] (F : ℕᵒᵖ ⥤ BoundedCoherentDerived X) {ι : Type*} [Finite ι]
    (W : ι → X.Opens) (hW : ⨆ i, W i = ⊤) :
    ProIsoDeligneSystem j F ↔
      ∀ i, ProIsoDeligneSystem (j ∣_ W i) (F ⋙ restrictBoundedCoherentLift (W i).ι) := by
  refine ⟨fun h i => h.restrict (W i).ι (j ∣_ W i) (range_morphismRestrict j (W i)), fun h => ?_⟩
  classical
  have := Fintype.ofFinite ι
  set U₀ := j.opensRange with hU₀
  have hr : Set.range U₀.ι.base = Set.range j.base := by
    rw [Scheme.Opens.range_ι, hU₀, Scheme.Hom.coe_opensRange]
  rw [← ProIsoDeligneSystem.congr_range hr]
  have h' : ∀ i, ProIsoDeligneSystem (U₀.ι ∣_ W i) (F ⋙ restrictBoundedCoherentLift (W i).ι) :=
    fun i => (ProIsoDeligneSystem.congr_range (by
      rw [range_morphismRestrict, range_morphismRestrict, hr])).mp (h i)
  have key (s : Finset ι) :
      ProIsoDeligneSystem (U₀.ι ∣_ s.sup W) (F ⋙ restrictBoundedCoherentLift (s.sup W).ι) := by
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sup_empty]
      have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x => by simpa using x.2⟩
      exact proIsoDeligneSystem_of_isEmpty _
    | insert a s _ ih =>
      rw [Finset.sup_insert]
      exact proIsoDeligneSystem_sup U₀ _ _ F (h' a) ih
  have htop := key Finset.univ
  rw [Finset.sup_univ_eq_iSup, hW] at htop
  refine ProIsoDeligneSystem.of_natIso
    ((Functor.rightUnitor F).symm ≪≫
      Functor.isoWhiskerLeft F (restrictBoundedCoherentLiftIdIso.symm ≪≫
        restrictBoundedCoherentLiftCompIso X.topIso.inv (⊤ : X.Opens).ι (𝟙 X)
          X.toIso_inv_ι) ≪≫
      (Functor.associator _ _ _).symm)
    (htop.restrict X.topIso.inv U₀.ι ?_)
  rw [range_morphismRestrict]
  ext x
  change x ∈ Set.range U₀.ι.base ↔ (⊤ : X.Opens).ι.base (X.topIso.inv.base x) ∈ Set.range U₀.ι.base
  rw [apply_eq_of_comp_eq X.toIso_inv_ι]
  rfl

end AlgebraicGeometry

end
