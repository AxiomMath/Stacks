module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.ResidueFibreLimit
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.GaloisCoverNoetherian
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.GenericFibre
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.SectionedModel
public import StacksFrontier.AlgebraicGeometry.Limits.StageBaseChangeOpens

/-!
# Extending a Galois cover from the generic fibre over a quasi-compact quasi-separated base

[Stacks, Tag 0EZJ]: let `S` be a quasi-compact and quasi-separated integral normal scheme with
generic point `η`, let `f : X ⟶ S` be a quasi-compact and quasi-separated smooth morphism with
geometrically connected fibres, and let `σ` be a section of `f`. Let `Z ⟶ X_η` be a finite étale
Galois cover with group `G` of order invertible on `S` such that `Z` has a `κ(η)`-rational point
mapping to `σ(η)`. Then there exists a finite étale Galois cover `Y ⟶ X` with group `G` whose
restriction to `X_η` is `Z`.

The source deduces this from the Noetherian case, [Stacks, Tag 0EYJ], by a limit argument. The
Noetherian case is
`AlgebraicGeometry.exists_finiteEtaleGaloisCover_extending_genericFiber_of_isNoetherian`,
whose named argument `h0EYD` is carried here.

## Main results

* `AlgebraicGeometry.exists_finiteEtaleGaloisCover_extending_genericFiber`: Tag 0EZJ, granted
  the input `h0EYD` of Tag 0EYJ.

## Implementation notes

The limit argument runs as in the source.

* `S` is the limit of integral normal Noetherian schemes `Sᵢ` with affine transition morphisms
  and dominant projections (`AlgebraicGeometry.exists_isLimit_isNoetherian_isIntegral_isNormal`).
* `f` and `σ` descend to a smooth `Xᵢ ⟶ Sᵢ` with geometrically connected fibres and a section,
  and `|G|` becomes invertible on a stage (`AlgebraicGeometry.GaloisCoverLimits`).
* The generic fibre `X_η` is the limit of the fibres of the `Xⱼ ⟶ Sⱼ` at the images `ηⱼ` of
  `η`, which are the generic points; so `Z` with its action and its rational point descends to a
  Galois cover of a generic fibre `X_{j, ηⱼ}` with a rational point over `σⱼ(ηⱼ)`.
* The Noetherian case extends it to `Yⱼ ⟶ Xⱼ`, and `Y = Yⱼ ×_{Xⱼ} X` is the cover sought. Its
  total space is connected because its generic fibre `Z` is and `Y ⟶ S` is flat and locally of
  finite presentation, so that the generic fibre is dense.

The comparison of the generic fibre of `X` with the limit of the generic fibres of the stages is
`Stacks.AlgebraicGeometry.Fibres.fiberConeIsLimit`, whose vertex is the fibre `f.fiber η` on the
nose. The fibres of the stages are taken at `ηⱼ`, the image of `η`, which is the generic point of
`Sⱼ` only propositionally; the Noetherian case is read at such a point by substituting the
equality.

## References

* [Stacks Project, Tag 0EZJ](https://stacks.math.columbia.edu/tag/0EZJ)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace GaloisCoverLimits

/-- The Noetherian case read at a point equal to the generic point. -/
theorem noetherianCase_at
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsIntegral S] [IsNormal S]
    [Smooth f] [GeometricallyConnected f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (G : Type v) [Group G] [Finite G]
    (hG : ∀ s : S, IsUnit (Nat.card G : S.residueField s))
    (y : S) (hy : y = genericPoint S)
    (Z : FiniteEtaleGaloisCover (f.fiber y) G)
    (z : Spec (S.residueField y) ⟶ Z.obj.left)
    (hz : z ≫ Z.obj.hom = pullback.lift (S.fromSpecResidueField y ≫ σ) (𝟙 _) (by
      rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])) :
    ∃ (Y : FiniteEtaleGaloisCover X G)
      (e : (finiteEtaleBaseChange (f.fiberι y)).obj Y.obj ≅ Z.obj),
      ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (f.fiberι y)).map (Y.action g).asIso.hom ≫ e.hom =
        e.hom ≫ (Z.action g).asIso.hom := by
  subst hy
  exact exists_finiteEtaleGaloisCover_extending_genericFiber_of_isNoetherian h0EYD
    f σ hσ G hG Z z hz

/-- Pasting a cartesian square onto the base change of `y` along `pX` gives a cartesian square
through the induced map into the pullback. -/
private theorem isPullback_pullbackLift_of_isPullback {C : Type*} [Category C] {P F X A Y : C}
    {n : P ⟶ Y} {h : P ⟶ F} {y : Y ⟶ A} {q : F ⟶ X} {pX : X ⟶ A} [HasPullback y pX]
    (hn : IsPullback n h y (q ≫ pX)) :
    IsPullback (pullback.lift n (h ≫ q) (by rw [hn.w, Category.assoc])) h
      (pullback.snd y pX) q := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback y pX)
  rwa [pullback.lift_fst]

/-- An equivariant cartesian square from a Galois cover `Z` of `F` to a Galois cover `Y'` of `A`,
over `q ≫ pX`, makes `Z` equivariantly the restriction along `q` of the base change of `Y'`
along `pX`. -/
private theorem exists_equivariant_iso_baseChange_of_isPullback {X A F : Scheme.{u}} (pX : X ⟶ A)
    (q : F ⟶ X) {G : Type v} [Group G] [Finite G] (Y' : FiniteEtaleGaloisCover A G)
    (Z : FiniteEtaleGaloisCover F G) (n : Z.obj.left ⟶ Y'.obj.left)
    (hn : IsPullback n Z.obj.hom Y'.obj.hom (q ≫ pX))
    (hact : ∀ g, (Z.action g).asIso.hom.left ≫ n = n ≫ (Y'.action g).asIso.hom.left)
    (hconn : ConnectedSpace ((finiteEtaleBaseChange pX).obj Y'.obj).left) :
    ∃ e : (finiteEtaleBaseChange q).obj (Y'.baseChange pX hconn).obj ≅ Z.obj,
      ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange q).map ((Y'.baseChange pX hconn).action g).asIso.hom ≫
        e.hom = e.hom ≫ (Z.action g).asIso.hom := by
  let pZ : Z.obj.left ⟶ pullback Y'.obj.hom pX :=
    pullback.lift n (Z.obj.hom ≫ q) (by rw [hn.w, Category.assoc])
  have hpZ₁ : pZ ≫ pullback.fst Y'.obj.hom pX = n := pullback.lift_fst _ _ _
  have hpZ₂ : pZ ≫ pullback.snd Y'.obj.hom pX = Z.obj.hom ≫ q := pullback.lift_snd _ _ _
  have hpZ (g : Gᵐᵒᵖ) :
      (Z.action g).asIso.hom.left ≫ pZ =
        pZ ≫ ((Y'.baseChange pX hconn).action g).asIso.hom.left := by
    have hY : ((Y'.baseChange pX hconn).action g).asIso.hom.left ≫ pullback.snd Y'.obj.hom pX =
        pullback.snd Y'.obj.hom pX :=
      MorphismProperty.Over.w ((Y'.baseChange pX hconn).action g).asIso.hom
    have hZ : (Z.action g).asIso.hom.left ≫ Z.obj.hom = Z.obj.hom :=
      MorphismProperty.Over.w (Z.action g).asIso.hom
    apply pullback.hom_ext
    · exact ((Category.assoc _ _ _).trans ((congrArg _ hpZ₁).trans (hact g))).trans
        ((Category.assoc _ _ _).trans ((congrArg (pZ ≫ ·)
          (FiniteEtaleGaloisCover.baseChange_action_fst pX Y' hconn g)).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hpZ₁)))).symm
    · exact ((Category.assoc _ _ _).trans ((congrArg _ hpZ₂).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hZ)))).trans
        ((Category.assoc _ _ _).trans ((congrArg (pZ ≫ ·) hY).trans hpZ₂)).symm
  exact exists_equivariant_iso_of_isPullback q (Y'.baseChange pX hconn).obj Z.obj pZ
    (isPullback_pullbackLift_of_isPullback hn)
    (fun g : Gᵐᵒᵖ ↦ ((Y'.baseChange pX hconn).action g).asIso.hom)
    (fun g : Gᵐᵒᵖ ↦ (Z.action g).asIso.hom) hpZ

/-- A pointed Galois cover of the generic fibre of a smooth sectioned family over a Noetherian
integral normal base, pulling back to `Z` along a map of generic fibres, extends `Z` to `X`. -/
private theorem exists_extending_genericFiber_of_pointed_noetherian_model
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    {S X T W : Scheme.{u}} [IsIntegral S] (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (fT : W ⟶ T) [IsNoetherian T] [IsIntegral T] [IsNormal T] [Smooth fT]
    [GeometricallyConnected fT] (σT : T ⟶ W) (hσT : σT ≫ fT = 𝟙 T)
    (G : Type v) [Group G] [Finite G] (hG : ∀ t : T, IsUnit (Nat.card G : T.residueField t))
    (y : T) (hy : y = genericPoint T) (V : FiniteEtaleGaloisCover (fT.fiber y) G)
    (w : Spec (T.residueField y) ⟶ V.obj.left)
    (hw : w ≫ V.obj.hom = pullback.lift (T.fromSpecResidueField y ≫ σT) (𝟙 _) (by
      rw [Category.assoc, hσT, Category.comp_id, Category.id_comp]))
    (pX : X ⟶ W) (b : f.fiber (genericPoint S) ⟶ fT.fiber y)
    (hb : b ≫ fT.fiberι y = f.fiberι (genericPoint S) ≫ pX)
    (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G) (P : Z.obj.left ⟶ V.obj.left)
    (hP : IsPullback P Z.obj.hom V.obj.hom b)
    (hPact : ∀ g, (Z.action g).asIso.hom.left ≫ P = P ≫ (V.action g).asIso.hom.left) :
    ∃ (Y : FiniteEtaleGaloisCover X G)
      (e : (finiteEtaleBaseChange (f.fiberι (genericPoint S))).obj Y.obj ≅ Z.obj),
      ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (f.fiberι (genericPoint S))).map (Y.action g).asIso.hom ≫
        e.hom = e.hom ≫ (Z.action g).asIso.hom := by
  classical
  obtain ⟨Y', e', he'⟩ := noetherianCase_at h0EYD fT σT hσT G hG y hy V w hw
  obtain ⟨n, hn, hnact⟩ := exists_equivariant_isPullback_of_iso (fT.fiberι y) Y'.obj V.obj e'
    (fun g : Gᵐᵒᵖ ↦ (Y'.action g).asIso.hom) (fun g : Gᵐᵒᵖ ↦ (V.action g).asIso.hom) he'
  have hchain : IsPullback (P ≫ n) Z.obj.hom Y'.obj.hom (f.fiberι (genericPoint S) ≫ pX) := by
    rw [← hb]
    exact hP.paste_horiz hn
  have hY'₁ : IsFinite Y'.obj.hom := Y'.obj.prop.1
  have hY'₂ : Etale Y'.obj.hom := Y'.obj.prop.2
  have hconn : ConnectedSpace ((finiteEtaleBaseChange pX).obj Y'.obj).left := by
    let g : pullback Y'.obj.hom pX ⟶ S := pullback.snd Y'.obj.hom pX ≫ f
    have hfib := (isPullback_pullbackLift_of_isPullback hchain).paste_vert
      (IsPullback.of_hasPullback f (S.fromSpecResidueField (genericPoint S)))
    have hg₁ : Flat g := inferInstanceAs (Flat (pullback.snd Y'.obj.hom pX ≫ f))
    have hg₂ : LocallyOfFinitePresentation g :=
      inferInstanceAs (LocallyOfFinitePresentation (pullback.snd Y'.obj.hom pX ≫ f))
    have hg₃ : ConnectedSpace (g.fiber (genericPoint S)) :=
      hfib.isoPullback.hom.homeomorph.connectedSpace_iff.mp Z.connected
    exact @connectedSpace_of_connectedSpace_genericFiber _ _ _ g hg₁ hg₂ hg₃
  obtain ⟨eZ, heZ⟩ := exists_equivariant_iso_baseChange_of_isPullback pX
    (f.fiberι (genericPoint S)) Y' Z (P ≫ n) hchain
    (fun g ↦ by rw [← Category.assoc, hPact, Category.assoc, hnact, Category.assoc]) hconn
  exact ⟨_, eZ, heZ⟩

section StageSection

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (k : I) (X : Over (D.obj k))
  (σ : D.obj k ⟶ X.left) (hσ : σ ≫ X.hom = 𝟙 _)

/-- The section of the stage base change diagram `m ↦ D m ×_{D k} X` induced by a section `σ`
of `X ⟶ D k`. -/
private def stageBaseChangeSection (m : Over k) :
    (Over.forget k ⋙ D).obj m ⟶ (stageBaseChangeDiagram D k X).obj m :=
  pullback.lift (𝟙 _) (D.map m.hom ≫ σ) (by
    rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])

/-- The section `stageBaseChangeSection` composed with the first projection to `D m` is the
identity. -/
private theorem stageBaseChangeSection_fst (m : Over k) :
    stageBaseChangeSection D k X σ hσ m ≫ pullback.fst (D.map m.hom) X.hom = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The section `stageBaseChangeSection` composed with the second projection to `X` is
`D.map m.hom ≫ σ`. -/
private theorem stageBaseChangeSection_snd (m : Over k) :
    stageBaseChangeSection D k X σ hσ m ≫ pullback.snd (D.map m.hom) X.hom = D.map m.hom ≫ σ :=
  pullback.lift_snd _ _ _

/-- The sections of the stage base change diagram are natural. -/
private theorem stageBaseChangeSection_naturality {m m' : Over k} (g : m ⟶ m') :
    (Over.forget k ⋙ D).map g ≫ stageBaseChangeSection D k X σ hσ m' =
      stageBaseChangeSection D k X σ hσ m ≫ (stageBaseChangeDiagram D k X).map g := by
  apply pullback.hom_ext
  · change D.map g.left ≫ stageBaseChangeSection D k X σ hσ m' ≫ pullback.fst (D.map m'.hom) X.hom =
      stageBaseChangeSection D k X σ hσ m ≫ pullback.lift (pullback.fst _ _ ≫ D.map g.left)
        (pullback.snd _ _) _ ≫ pullback.fst (D.map m'.hom) X.hom
    rw [stageBaseChangeSection_fst, pullback.lift_fst, ← Category.assoc,
      stageBaseChangeSection_fst, Category.id_comp]
    exact Category.comp_id _
  · change D.map g.left ≫ stageBaseChangeSection D k X σ hσ m' ≫ pullback.snd (D.map m'.hom) X.hom =
      stageBaseChangeSection D k X σ hσ m ≫ pullback.lift (pullback.fst _ _ ≫ D.map g.left)
        (pullback.snd _ _) _ ≫ pullback.snd (D.map m'.hom) X.hom
    rw [stageBaseChangeSection_snd, pullback.lift_snd, stageBaseChangeSection_snd,
      ← Category.assoc, ← D.map_comp, Over.w g]

end StageSection

/-- The extension of `Z` to `X` over a limit `S` of integral normal Noetherian stages with
dominant projections, given a smooth model `X₁ ⟶ D k` of `f` with a section compatible with `σ`,
on whose stage `|G|` is invertible. -/
private theorem exists_extending_genericFiber_of_sectioned_model
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    {I : Type u} [Category.{u} I] [IsCofiltered I] {S : Scheme.{u}} [IsIntegral S]
    {D : I ⥤ Scheme.{u}} (π : (Functor.const I).obj S ⟶ D) (hc : IsLimit (Cone.mk S π))
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, IsNoetherian (D.obj i)]
    [∀ i, IsIntegral (D.obj i)] [∀ i, IsNormal (D.obj i)] (hdom : ∀ i, IsDominant (π.app i))
    {X : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) (k : I) (X₁ : Over (D.obj k)) [QuasiCompact X₁.hom]
    [QuasiSeparated X₁.hom] [Smooth X₁.hom] [GeometricallyConnected X₁.hom]
    (σ₁ : D.obj k ⟶ X₁.left) (hσ₁ : σ₁ ≫ X₁.hom = 𝟙 _) (p₁ : X ⟶ X₁.left)
    (hp₁ : IsPullback p₁ f X₁.hom (π.app k)) (hs₁ : σ ≫ p₁ = π.app k ≫ σ₁)
    (G : Type v) [Group G] [Finite G]
    (hG : ∀ t : D.obj k, IsUnit (Nat.card G : (D.obj k).residueField t))
    (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)
    (z : Spec (S.residueField (genericPoint S)) ⟶ Z.obj.left)
    (hz : z ≫ Z.obj.hom = genericFiberSection f σ hσ) :
    ∃ (Y : FiniteEtaleGaloisCover X G)
      (e : (finiteEtaleBaseChange (f.fiberι (genericPoint S))).obj Y.obj ≅ Z.obj),
      ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (f.fiberι (genericPoint S))).map (Y.action g).asIso.hom ≫
        e.hom = e.hom ≫ (Z.action g).asIso.hom := by
  let c := Cone.mk S π
  let A := stageBaseChangeDiagram D k X₁
  let φ : A ⟶ Over.forget k ⋙ D := stageBaseChangeDiagramι D k X₁
  let cB : Cone (Over.forget k ⋙ D) := c.whisker (Over.forget k)
  have hB : IsLimit cB := (Functor.Initial.isLimitWhiskerEquiv (Over.forget k) c).symm hc
  let cA₀ := stageBaseChangeCone D c k X₁
  have hA₀ : IsLimit cA₀ := stageBaseChangeConeIsLimit D c hc k X₁
  let ι : X ≅ pullback (c.π.app k) X₁.hom := hp₁.flip.isoPullback
  let cA := cA₀.extend ι.hom
  have hA : IsLimit cA := hA₀.ofIsoLimit (Cone.extendIso cA₀ ι.symm)
  have hcA (m : Over k) : cA.π.app m = hp₁.flip.isoPullback.hom ≫ pullback.lift
      (pullback.fst (c.π.app k) X₁.hom ≫ c.π.app m.left) (pullback.snd (c.π.app k) X₁.hom)
      (by rw [Category.assoc, c.w, pullback.condition]) := rfl
  have hcA₁ (m : Over k) : cA.π.app m ≫ pullback.fst (D.map m.hom) X₁.hom = f ≫ c.π.app m.left := by
    rw [hcA, Category.assoc, pullback.lift_fst, ← Category.assoc, hp₁.flip.isoPullback_hom_fst]
  have hcA₂ (m : Over k) : cA.π.app m ≫ pullback.snd (D.map m.hom) X₁.hom = p₁ := by
    rw [hcA, Category.assoc, pullback.lift_snd, hp₁.flip.isoPullback_hom_snd]
  have hsq (m : Over k) : IsPullback (cA.π.app m) f (φ.app m) (cB.π.app m) := by
    have ho : IsPullback (cA.π.app m ≫ pullback.snd (D.map m.hom) X₁.hom) f X₁.hom
        (c.π.app m.left ≫ D.map m.hom) := by rwa [hcA₂, c.w m.hom]
    exact ho.of_right (hcA₁ m) (IsPullback.of_hasPullback (D.map m.hom) X₁.hom).flip
  have hAaff {m m' : Over k} (g : m ⟶ m') : IsAffineHom (A.map g) :=
    stageBaseChangeDiagram_map_isAffineHom D k X₁ g
  have hBaff {m m' : Over k} (g : m ⟶ m') : IsAffineHom ((Over.forget k ⋙ D).map g) :=
    inferInstanceAs (IsAffineHom (D.map g.left))
  have hφqc (m : Over k) : QuasiCompact (φ.app m) :=
    inferInstanceAs (QuasiCompact (pullback.fst (D.map m.hom) X₁.hom))
  have hφqs (m : Over k) : QuasiSeparated (φ.app m) :=
    inferInstanceAs (QuasiSeparated (pullback.fst (D.map m.hom) X₁.hom))
  have hlim (m : Over k) :
      σ ≫ cA.π.app m = cB.π.app m ≫ stageBaseChangeSection D k X₁ σ₁ hσ₁ m := by
    apply pullback.hom_ext
    · rw [Category.assoc, hcA₁, ← Category.assoc, hσ, Category.id_comp, Category.assoc,
        stageBaseChangeSection_fst, Category.comp_id]
      rfl
    · rw [Category.assoc, hcA₂, hs₁, Category.assoc, stageBaseChangeSection_snd, ← Category.assoc]
      exact congrArg (· ≫ σ₁) (c.w m.hom).symm
  obtain ⟨m, V, P, w, hP, hPact, hw⟩ := exists_pointed_galoisCover_model φ cB (genericPoint S)
    cA f hcA₁ hA hB hsq (stageBaseChangeSection D k X₁ σ₁ hσ₁)
    (stageBaseChangeSection_fst D k X₁ σ₁ hσ₁) (stageBaseChangeSection_naturality D k X₁ σ₁ hσ₁)
    σ hσ hlim Z z hz
  have : IsDominant (c.π.app m.left) := hdom m.left
  have hGT (t : D.obj m.left) : IsUnit (Nat.card G : (D.obj m.left).residueField t) := by
    simpa using (hG (D.map m.hom t)).map ((D.map m.hom).residueFieldMap t).hom
  exact exists_extending_genericFiber_of_pointed_noetherian_model h0EYD f
    (pullback.fst (D.map m.hom) X₁.hom) (stageBaseChangeSection D k X₁ σ₁ hσ₁ m)
    (stageBaseChangeSection_fst D k X₁ σ₁ hσ₁ m) G hGT _
    (genericPoint_eq_of_isDominant (X := S) (c.π.app m.left)) V w hw (cA.π.app m) _
    (ptFiberConeMap_fst φ cB (genericPoint S) cA f hcA₁ m) Z P hP hPact

end GaloisCoverLimits

open GaloisCoverLimits NormalApproximation in
/-- **Stacks Project, Tag 0EZJ**, granted the input of the Noetherian case Tag 0EYJ. Let `S` be a
quasi-compact and quasi-separated integral normal scheme with generic point `η`, let
`f : X ⟶ S` be a quasi-compact and quasi-separated smooth morphism with geometrically connected
fibres and `σ` a section of `f`. Let `Z ⟶ X_η` be a finite étale Galois cover with group `G` of
order invertible on `S` such that `Z` has a `κ(η)`-rational point mapping to `σ(η)`. Then there is
a finite étale Galois cover `Y ⟶ X` with group `G` whose restriction to `X_η` is `Z`,
equivariantly.

The named argument `h0EYD` (the tame half of
[Stacks, Tag 0EYD]) is that of the Noetherian case
`AlgebraicGeometry.exists_finiteEtaleGaloisCover_extending_genericFiber_of_isNoetherian`. -/
theorem exists_finiteEtaleGaloisCover_extending_genericFiber
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    {S X : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsIntegral S] [IsNormal S]
    [QuasiCompact f] [QuasiSeparated f] [Smooth f] [GeometricallyConnected f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (G : Type v) [Group G] [Finite G]
    (hG : ∀ s : S, IsUnit (Nat.card G : S.residueField s))
    (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint S)) G)
    (z : Spec (S.residueField (genericPoint S)) ⟶ Z.obj.left)
    (hz : z ≫ Z.obj.hom = genericFiberSection f σ hσ) :
    ∃ (Y : FiniteEtaleGaloisCover X G)
      (e : (finiteEtaleBaseChange (f.fiberι (genericPoint S))).obj Y.obj ≅ Z.obj),
      ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (f.fiberι (genericPoint S))).map (Y.action g).asIso.hom ≫
        e.hom = e.hom ≫ (Z.action g).asIso.hom := by
  classical
  obtain ⟨I, _, _, D, π, ⟨hc⟩, haff, hNoeth, hInt, hNormal, hdom⟩ :=
    exists_isLimit_isNoetherian_isIntegral_isNormal S
  let c := Cone.mk S π
  have : ∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g) := haff
  have : ∀ i, IsNoetherian (D.obj i) := hNoeth
  have : ∀ i, IsIntegral (D.obj i) := hInt
  have : ∀ i, IsNormal (D.obj i) := hNormal
  have hfp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨j, Y₀, f₀, σ₀, p₀, hf₀, hsm₀, hgc₀, hσ₀, hpb₀, hs₀⟩ :=
    exists_sectioned_smooth_model D c hc f hfp σ hσ
  obtain ⟨k, e, hGk⟩ := exists_stage_isUnit_natCast D c hc (Nat.card G) hG j
  obtain ⟨σ₁, p₁, hσ₁, -, -, hp₁, hs₁⟩ :=
    sectionedModel_baseChange D c f σ hσ e f₀ σ₀ p₀ hσ₀ hpb₀ hs₀
  have hf₀₁ : QuasiCompact f₀ := hf₀.2.1
  have hf₀₂ : QuasiSeparated f₀ := hf₀.2.2
  let X₁ : Over (D.obj k) := Over.mk (pullback.snd f₀ (D.map e))
  have hX₁₁ : QuasiCompact X₁.hom := inferInstanceAs (QuasiCompact (pullback.snd f₀ (D.map e)))
  have hX₁₂ : QuasiSeparated X₁.hom :=
    inferInstanceAs (QuasiSeparated (pullback.snd f₀ (D.map e)))
  have hX₁₃ : Smooth X₁.hom := inferInstanceAs (Smooth (pullback.snd f₀ (D.map e)))
  have hX₁₄ : GeometricallyConnected X₁.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd f₀ (D.map e)))
  exact exists_extending_genericFiber_of_sectioned_model h0EYD π hc hdom f σ hσ k X₁ σ₁
    hσ₁ p₁ hp₁ hs₁ G hGk Z z hz

end AlgebraicGeometry

end
