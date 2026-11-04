module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.IdealPowerSystemProIso

/-!
# The Deligne system of a coherent module placed in one degree

Let `X` be a Noetherian scheme, `U ⊆ X` open, `𝓘 ⊆ 𝒪_X` a quasi-coherent sheaf of ideals cutting
out `X ∖ U` and `𝓕` a coherent `𝒪_X`-module. The Deligne system of the complex `𝓕[-p]`, which has
`𝓕` in degree `p` and zero elsewhere, is `(𝓘^n𝓕[-p])`: its ideal-power subcomplexes are the
modules `𝓘^n𝓕` placed in degree `p`, with the inclusions `𝓘^(n+1)𝓕 ⊆ 𝓘^n𝓕` as transitions.

## Main definitions

* `AlgebraicGeometry.singleDeligneSystem`: the Deligne system `(𝓘^n𝓕[-p])`.
* `AlgebraicGeometry.singleDeligneSystemIso`: its underlying system in `D(𝒪_X)` is the inverse
  system `(𝓘^n𝓕)` placed in degree `p`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The Deligne system `(𝓘^n𝓕[-p])` of a coherent module `𝓕` placed in degree `p`. -/
public abbrev singleDeligneSystem [IsNoetherian X] (W : X.Opens) (I : X.IdealSheafData)
    (hI : (I.support : Set X) = (Set.range W.ι.base)ᶜ) (F : X.Modules) [F.IsCoherent] (p : ℤ) :
    DeligneSystem W.ι :=
  DeligneTriangle.deligneSystemOfComplex W.ι I hI
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p).obj F)
    ⟨p, inferInstanceAs (CochainComplex.IsStrictlyGE
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p).obj F) p)⟩
    ⟨p, inferInstanceAs (CochainComplex.IsStrictlyLE
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p).obj F) p)⟩
    (DeligneSystem.isCoherent_single_X F p)

namespace SingleDeligneSystem

open Stacks.AlgebraicGeometry.IdealPower

variable (I : X.IdealSheafData) (F : X.Modules) (p : ℤ)

/-- The ideal-power subcomplexes `𝓘^n(𝓕[-p])` of the complex `𝓕[-p]`. -/
abbrev powers : IdealPowerComplexSystem I
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p).obj F) :=
  idealPowerComplexSystem I ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p).obj F)

/-- The comparison `𝓘^n(𝓕[-p])^p ⟶ 𝓘^n𝓕` in degree `p`, induced by `(𝓕[-p])^p ≅ 𝓕`. -/
def toTerm (n : ℕ) :
    ((powers I F p).complex n).X p ⟶
      ((Stacks.Algebraization.idealPowerMultiple I n F).toSheafOfModules : X.Modules) :=
  ((powers I F p).termIso n p).hom ≫
    sheafSubmoduleMap (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p F).hom _ _
      (idealPowerMultiple_le_comap I n _ _
        (Stacks.Duality.idealPowerMultiple_eq_algebraization I n F).le)

/-- The comparison `𝓘^n𝓕 ⟶ 𝓘^n(𝓕[-p])^p` in degree `p`, induced by `𝓕 ≅ (𝓕[-p])^p`. -/
def ofTerm (n : ℕ) :
    ((Stacks.Algebraization.idealPowerMultiple I n F).toSheafOfModules : X.Modules) ⟶
      ((powers I F p).complex n).X p :=
  sheafSubmoduleMap (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p F).inv _ _
      (by
        rw [← Stacks.Duality.idealPowerMultiple_eq_algebraization]
        exact idealPowerMultiple_le_comap I n _ _ le_rfl) ≫
    ((powers I F p).termIso n p).inv

/-- Followed by the inclusion `𝓘^n𝓕 ⊆ 𝓕`, the degree-`p` comparison is the inclusion
`𝓘^n(𝓕[-p])^p ⊆ (𝓕[-p])^p` followed by `(𝓕[-p])^p ≅ 𝓕`. -/
lemma toTerm_ι (n : ℕ) :
    toTerm I F p n ≫ subι (Stacks.Algebraization.idealPowerMultiple I n F) =
      ((powers I F p).inclusion n).f p ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p F).hom :=
  (Category.assoc _ _ _).trans ((whisker_eq _ (sheafSubmoduleMap_comp_ι _ _ _ _)).trans
    ((Category.assoc _ _ _).symm.trans (eq_whisker ((powers I F p).include_f n p) _)))

/-- Followed by the inclusion `𝓘^n(𝓕[-p])^p ⊆ (𝓕[-p])^p`, the inverse degree-`p` comparison is
the inclusion `𝓘^n𝓕 ⊆ 𝓕` followed by `𝓕 ≅ (𝓕[-p])^p`. -/
lemma ofTerm_inclusion (n : ℕ) :
    ofTerm I F p n ≫ ((powers I F p).inclusion n).f p =
      subι (Stacks.Algebraization.idealPowerMultiple I n F) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p F).inv :=
  (Category.assoc _ _ _).trans ((whisker_eq _ ((whisker_eq _
    ((powers I F p).include_f n p).symm).trans
    (Iso.inv_hom_id_assoc _ _))).trans (sheafSubmoduleMap_comp_ι _ _ _ _))

/-- Outside degree `p` the ideal-power subcomplexes of `𝓕[-p]` vanish. -/
lemma isZero_complex_X (n : ℕ) (i : ℤ) (hi : i ≠ p) :
    IsZero (((powers I F p).complex n).X i) :=
  have := mono_subι (idealPowerMultiple I n
    (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p).obj F).X i))
  (IsZero.of_mono (subι (idealPowerMultiple I n
    (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p).obj F).X i)))
    (HomologicalComplex.isZero_single_obj_X _ p F i hi)).of_iso ((powers I F p).termIso n i)

/-- The inclusion `𝓘^n(𝓕[-p]) ⊆ 𝓕[-p]` is a monomorphism in each degree. -/
instance mono_inclusion_f (n : ℕ) (i : ℤ) : Mono (((powers I F p).inclusion n).f i) :=
  ⟨fun g h e => (Iso.cancel_iso_hom_right g h ((powers I F p).termIso n i)).1
    (cancel_subι _ _ _ ((Category.assoc _ _ _).trans
      ((whisker_eq _ ((powers I F p).include_f n i)).trans (e.trans
        (whisker_eq _ ((powers I F p).include_f n i)).symm) |>.trans
          (Category.assoc _ _ _).symm)))⟩

/-- The two degree-`p` comparisons are mutually inverse: first composite. -/
lemma toTerm_ofTerm (n : ℕ) : toTerm I F p n ≫ ofTerm I F p n = 𝟙 _ :=
  (cancel_mono (((powers I F p).inclusion n).f p)).1 ((Category.assoc _ _ _).trans
    ((whisker_eq _ (ofTerm_inclusion I F p n)).trans ((Category.assoc _ _ _).symm.trans
      ((eq_whisker (toTerm_ι I F p n) _).trans (by simp)))))

/-- The two degree-`p` comparisons are mutually inverse: second composite. -/
lemma ofTerm_toTerm (n : ℕ) : ofTerm I F p n ≫ toTerm I F p n = 𝟙 _ :=
  cancel_subι _ _ _ ((Category.assoc _ _ _).trans
    ((whisker_eq _ (toTerm_ι I F p n)).trans ((Category.assoc _ _ _).symm.trans
      ((eq_whisker (ofTerm_inclusion I F p n) _).trans ((Category.assoc _ _ _).trans
        ((whisker_eq _ (Iso.inv_hom_id _)).trans
          ((Category.comp_id _).trans (Category.id_comp _).symm)))))))

/-- The comparison map from `𝓘^n(𝓕[-p])` to `𝓘^n𝓕` placed in degree `p`. -/
def complexHom (n : ℕ) :
    (powers I F p).complex n ⟶
      (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p).obj
        ((Stacks.Algebraization.idealPowerMultiple I n F).toSheafOfModules : X.Modules) :=
  HomologicalComplex.mkHomToSingle (toTerm I F p n) (fun i hi =>
    (isZero_complex_X I F p n i (by rw [ComplexShape.up_Rel] at hi; omega)).eq_of_src _ _)

/-- The comparison map from `𝓘^n𝓕` placed in degree `p` to `𝓘^n(𝓕[-p])`. -/
def complexInv (n : ℕ) :
    (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p).obj
        ((Stacks.Algebraization.idealPowerMultiple I n F).toSheafOfModules : X.Modules) ⟶
      (powers I F p).complex n :=
  HomologicalComplex.mkHomFromSingle (ofTerm I F p n) (fun k hk =>
    (isZero_complex_X I F p n k (by rw [ComplexShape.up_Rel] at hk; omega)).eq_of_tgt _ _)

/-- In degree `p`, the comparison of complexes is the comparison `toTerm`. -/
lemma complexHom_f (n : ℕ) :
    (complexHom I F p n).f p = toTerm I F p n ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p
        ((Stacks.Algebraization.idealPowerMultiple I n F).toSheafOfModules : X.Modules)).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

/-- In degree `p`, the inverse comparison of complexes is the comparison `ofTerm`. -/
lemma complexInv_f (n : ℕ) :
    (complexInv I F p n).f p =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p
        ((Stacks.Algebraization.idealPowerMultiple I n F).toSheafOfModules : X.Modules)).hom ≫
          ofTerm I F p n :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- The `n`-th ideal-power subcomplex of `𝓕[-p]` is `𝓘^n𝓕` placed in degree `p`. -/
def complexIso (n : ℕ) :
    (powers I F p).complex n ≅
      (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p).obj
        ((Stacks.Algebraization.idealPowerMultiple I n F).toSheafOfModules : X.Modules) where
  hom := complexHom I F p n
  inv := complexInv I F p n
  hom_inv_id := by
    refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
    by_cases hi : i = p
    · subst hi
      refine (HomologicalComplex.comp_f _ _ i).trans ?_
      refine (congrArg₂ (· ≫ ·) (complexHom_f I F i n) (complexInv_f I F i n)).trans ?_
      exact (Category.assoc _ _ _).trans
        ((whisker_eq _ (Iso.inv_hom_id_assoc _ _)).trans (toTerm_ofTerm I F i n))
    · exact (isZero_complex_X I F p n i hi).eq_of_src _ _
  inv_hom_id := by
    refine HomologicalComplex.from_single_hom_ext ?_
    refine (HomologicalComplex.comp_f _ _ p).trans ?_
    refine (congrArg₂ (· ≫ ·) (complexInv_f I F p n) (complexHom_f I F p n)).trans ?_
    exact (Category.assoc _ _ _).trans ((whisker_eq _ ((Category.assoc _ _ _).symm.trans
      ((eq_whisker (ofTerm_toTerm I F p n) _).trans (Category.id_comp _)))).trans
        (Iso.hom_inv_id _))

/-- In degree `p`, the comparison carries the transition `𝓘^(n+1)(𝓕[-p]) ⟶ 𝓘^n(𝓕[-p])` to the
inclusion `𝓘^(n+1)𝓕 ⊆ 𝓘^n𝓕`. -/
lemma transition_toTerm (n : ℕ) :
    ((powers I F p).transition n).f p ≫ toTerm I F p n =
      toTerm I F p (n + 1) ≫ subHom (idealPowerMultiple_antitone I F (Nat.le_succ n)) :=
  cancel_subι _ _ _ ((Category.assoc _ _ _).trans ((whisker_eq _ (toTerm_ι I F p n)).trans
    ((Category.assoc _ _ _).symm.trans ((eq_whisker
      ((HomologicalComplex.comp_f _ _ p).symm.trans
        (congrArg (fun φ => HomologicalComplex.Hom.f φ p)
          ((powers I F p).transition_include n))) _).trans
      ((toTerm_ι I F p (n + 1)).symm.trans ((whisker_eq _
        (homOfLE_comp_subι (idealPowerMultiple_antitone I F (Nat.le_succ n)))).symm.trans
          (Category.assoc _ _ _).symm))))))

/-- The comparison of complexes carries the transition `𝓘^(n+1)(𝓕[-p]) ⟶ 𝓘^n(𝓕[-p])` to the
inclusion `𝓘^(n+1)𝓕 ⊆ 𝓘^n𝓕` placed in degree `p`. -/
lemma transition_complexHom (n : ℕ) :
    (powers I F p).transition n ≫ complexHom I F p n =
      complexHom I F p (n + 1) ≫
        (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p).map
          (subHom (idealPowerMultiple_antitone I F (Nat.le_succ n))) := by
  refine HomologicalComplex.to_single_hom_ext ?_
  refine (HomologicalComplex.comp_f _ _ p).trans ((whisker_eq _ (complexHom_f I F p n)).trans ?_)
  refine Eq.trans ?_ (HomologicalComplex.comp_f _ _ p).symm
  refine Eq.trans ?_ (congrArg₂ (· ≫ ·) (complexHom_f I F p (n + 1)).symm
    (HomologicalComplex.single_map_f_self _ p _).symm)
  refine (Category.assoc _ _ _).symm.trans ((eq_whisker (transition_toTerm I F p n) _).trans ?_)
  exact (Category.assoc _ _ _).trans (whisker_eq _ (Iso.inv_hom_id_assoc _ _).symm) |>.trans
    (Category.assoc _ _ _).symm

/-- The comparison of the inverse system of complexes `(𝓘^n(𝓕[-p]))` with the inverse system
`(𝓘^n𝓕)` placed in degree `p`. -/
def systemHom :
    Functor.ofOpSequence (powers I F p).transition ⟶
      Stacks.Duality.idealPowerSystem I F ⋙
        HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p :=
  NatTrans.ofOpSequence (fun n => (complexIso I F p n).hom) (fun n => by
    rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.comp_map,
      show (Stacks.Duality.idealPowerSystem I F).map (homOfLE (n.le_add_right 1)).op =
        subHom (idealPowerMultiple_antitone I F (Nat.le_succ n)) from
        Functor.ofOpSequence_map_homOfLE_succ _ n]
    exact transition_complexHom I F p n)

/-- The comparison of inverse systems is an isomorphism, being one levelwise. -/
instance : IsIso (systemHom I F p) :=
  haveI : ∀ n : ℕᵒᵖ, IsIso ((systemHom I F p).app n) :=
    fun n => inferInstanceAs (IsIso (complexIso I F p n.unop).hom)
  NatIso.isIso_of_isIso_app _

/-- The ideal-power subcomplexes `𝓘^n(𝓕[-p])`, as an inverse system of complexes, are the inverse
system `(𝓘^n𝓕)` placed in degree `p`. -/
def systemIso :
    Functor.ofOpSequence (powers I F p).transition ≅
      Stacks.Duality.idealPowerSystem I F ⋙
        HomologicalComplex.single X.Modules (ComplexShape.up ℤ) p :=
  asIso (systemHom I F p)

end SingleDeligneSystem

open SingleDeligneSystem in
/-- **The Deligne system of a coherent module placed in one degree.** For a coherent
`𝒪_X`-module `𝓕`, the Deligne system `(𝓘^n𝓕[-p])` is, as an inverse system of `D(𝒪_X)`, the
inverse system `(𝓘^n𝓕)` of ideal-power multiples, with the inclusions as transitions, placed in
degree `p`. -/
public def singleDeligneSystemIso [IsNoetherian X] (W : X.Opens) (I : X.IdealSheafData)
    (hI : (I.support : Set X) = (Set.range W.ι.base)ᶜ) (F : X.Modules) [F.IsCoherent] (p : ℤ) :
    (singleDeligneSystem W I hI F p).system ⋙ (boundedCoherentDerived X).ι ≅
      Stacks.Duality.idealPowerSystem I F ⋙ DerivedCategory.singleFunctor X.Modules p :=
  (singleDeligneSystem W I hI F p).representation ≪≫
    Functor.isoWhiskerRight (systemIso I F p) DerivedCategory.Q ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.singleFunctorIsoCompQ X.Modules p).symm

end AlgebraicGeometry

end
